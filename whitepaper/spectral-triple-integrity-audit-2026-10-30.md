# Spectral-Triple Integrity Audit — 2026-10-30

NO CLAIM. Dials 0/4. Read-only audit: nothing under
`~/workspace/thet-logos` was edited, built, or repaired. Weak
statements are reported, never fixed — repairs are new entries on
Jeff's word, per the relabeling rule.

**Parent verification (landing, 2026-10-30):** the three
load-bearing findings were re-checked against disk by the parent —
the `exotic_decomposition` axiom and its in-file UNSOUND-AS-STATED
flag (CFKernelClassification.lean:122); the
`cf_kernel_classification_full` proof discarding h_sa/h_J/h_g
(CFKernelClassification.lean:246–250, its own comment: "46→10
kernel reduction needs only order-one + commutator"); and a fresh
`#print axioms ccm_classification` run returning exactly
[propext, Classical.choice, Quot.sound,
AdmitsClassifyingDirac_unpack, exoticBasisAux,
exotic_decomposition] as tabled below.

Question (Jeff, 2026-10-30): do the corpus's spectral triples hold
in concrete, or were they empty proofs?

## Verdict in one paragraph

The six spectral-triple modules are **not** empty proofs. Of 208
theorem/lemma headlines in the audited family (197 in the six
modules + 11 in the two classification modules), **205 are
proved-only** (axiom footprint ⊆ {propext, Classical.choice,
Quot.sound}, the standard three), **3 are conditional** on corpus
T4 file axioms (named below), and **sorryAx appears NOWHERE** —
the post-SORRY-0 expectation holds in this family. **2 headlines
are WEAK** by the OSReconstruction substance standard (named
below, both in the classification pair). The main structural
caveat is not weakness but *level*: ProductTriple / AnalyticTriple
/ BoundedTriple prove their theorems relative to **T2 class data**
(`TripleData`, `AnalyticTripleData`, `BoundedAnalyticTriple`) —
the algebra/Hilbert/Dirac/grading/real-structure relations are
class fields (hypotheses-as-data), so the footprints are
standard-only because no *file axiom* is consumed; no concrete
manifold factor, finite factor, or bounded triple is *constructed*
in these three modules (the one concrete instance, `pauliBounded`,
is in ConcreteBoundedTriple and is conditional, §4). The modules'
own headers disclose this level honestly at every point checked.

## Counts

| scope | headlines | (a) proved-only | (b) conditional | (c) sorryAx |
|---|---|---|---|---|
| FiniteSpectralTriple | 14 | 14 | 0 | 0 |
| ConcreteBoundedTriple (theorems) | 4 | 4 | 0 | 0 |
| BoundedTriple | 6 | 6 | 0 | 0 |
| AnalyticTriple | 17 | 17 | 0 | 0 |
| ProductTriple | 63 | 63 | 0 | 0 |
| TwistedTriple | 93 | 93 | 0 | 0 |
| CCMAlgebraClassification (all theorems) | 7 | 6 | 1 | 0 |
| CFKernelClassification (all theorems) | 4 | 2 | 2 | 0 |
| **Family total** | **208** | **205** | **3** | **0** |

Plus, outside the theorem count: the instance
`ConcreteBoundedTriple.pauliBounded` (ConcreteBoundedTriple.lean:142)
is bucket (b) — footprint = standard three +
`ThetLogos.pauli_compactResolvent` (the file's own labeled T2
axiom, ConcreteBoundedTriple.lean:131).

Nine headlines have an **empty** footprint (no axioms at all,
closed by `decide`/`rfl`): CCM's `smFactors_dim_ok`,
`smFactors_faithful`, `smFactors_orientable`,
`filters_do_not_classify`, `minimalBlock_sum`,
`singlet_remainder`, and ProductTriple's `flipProd_involutive`,
`flipProd_CM_regular`, `koDim_add`. Empty footprint is a subset
of bucket (a).

## Conditional headlines (bucket b) — every one, by name

1. `CFKernelClassification.cf_kernel_classification_46_10`
   (CFKernelClassification.lean:189) — axioms beyond standard:
   `ThetLogos.exoticBasisAux` (CFKernelClassification.lean:102),
   `ThetLogos.exotic_decomposition` (CFKernelClassification.lean:122).
   ⚠ The consumed axiom `exotic_decomposition` is flagged **in its
   own docstring** "UNSOUND AS STATED — FALSE AS STATED"
   (CFKernelClassification.lean:122–131): its domain is the weak
   144-pair `OrderOneHolds` nullspace while the 46-dim census was
   computed in the 272-real-dimensional admissible subspace.
2. `CFKernelClassification.cf_kernel_classification_full`
   (CFKernelClassification.lean:238) — same two axioms. Same ⚠
   (its header repeats the flag, CFKernelClassification.lean:238–245).
   Also WEAK — see below.
3. `CCMAlgebraClassification.ccm_classification`
   (CCMAlgebraClassification.lean:225) — axioms beyond standard:
   `ThetLogos.AdmitsClassifyingDirac_unpack`
   (CCMAlgebraClassification.lean:209), `ThetLogos.exoticBasisAux`,
   `ThetLogos.exotic_decomposition` (both via headline 1). Its
   header likewise flags it "UNSOUND AS STATED" via headline 1
   (CCMAlgebraClassification.lean:225–232). Also WEAK — see below.
4. (Instance, not a theorem) `ConcreteBoundedTriple.pauliBounded`
   (ConcreteBoundedTriple.lean:142) — `ThetLogos.pauli_compactResolvent`
   only. This is the disclosed "named window": the opaque
   `HasCompactResolvent` (BoundedTriple.lean:88–89) cannot be
   proved, only assumed; its mathematical content for the Pauli
   model *is* proved in the same file (`pauliD_resolvent`,
   `pauliD_resolvent_compact`, both bucket (a)).

No other corpus axioms are consumed anywhere in the family. In
particular none of the six modules' theorems depends on any axiom
declared in an imported dependency (Scaffold32, ConcreteFiniteModel,
FlowKernel, CFKernel, CFKernelBase, OrderOne, MartinettiRep declare
no file axioms at all — grep-verified).

## Weak headlines — every one, by name

**W1. `CCMAlgebraClassification.ccm_classification`
(CCMAlgebraClassification.lean:225).** Three of its four hypotheses
do no work: `h_dim : totalRepDim A = 16`, `h_faith : IsFaithful A =
true`, `h_c : HasComplexUnit A = true` are never used — the proof
(CCMAlgebraClassification.lean:236–241) uses only `h_dirac`. The
entire classification content is carried by the T4 axiom
`AdmitsClassifyingDirac_unpack` (CCMAlgebraClassification.lean:209–215),
whose conclusion already contains the reconstruction clause
`IsSMPhysicalSector D → A = smFactors` — i.e. the axiom assumes,
in conditional form, the algebra↔Dirac reconstruction the theorem
appears to prove. The theorem is an honest *conditional* (its
header says exactly this), but as a *statement* it is weaker than
its shape suggests: delete the three filter hypotheses and nothing
changes. (The module itself proves the filters insufficient —
`filters_do_not_classify`, CCMAlgebraClassification.lean:107,
bucket (a), empty footprint — which is the substantive negative
result of the file.)

**W2. `CFKernelClassification.cf_kernel_classification_full`
(CFKernelClassification.lean:238).** Hypothesis-never-used: of its
five hypotheses, `h_sa` (self-adjointness), `h_J`
(J-compatibility), `h_g` (grading-oddness) are never used — the
proof (CFKernelClassification.lean:248–250) discards them and
reduces to headline 1 on `h_oo` + `h_cf` alone (the proof comment
admits this). So the "full spectral-triple version" framing in
the dossier English (see §6) overstates the statement: the extra
spectral-triple hypotheses constrain nothing in the conclusion's
derivation. (They are not *false* — the 10 SM generators do satisfy
them — but the theorem as stated does not use them.)

No other headline in the 208 meets the weak criteria
(∀∃True shape, hypothesis never used, conclusion about different
data than the hypotheses constrain, existence claimed for a
structure whose defining conditions are absent). A group of
headlines is **trivial-but-exact** (proof by `rfl`/`decide`,
footprint empty or standard, and *labeled as definitional in
their own docstrings*); they are listed in §5.3, not counted weak.

## Method & timing

Per-module driver files (one import each; no all-import
environment — two tree modules define `ThetLogos.Config`) written
to `/tmp/audit-drivers/`, run with `lake env lean` from
`~/workspace/thet-logos/lean`, PATH prepended with `~/.elan/bin`,
Mathlib pinned v4.35.0-rc3 per `lean-toolchain`. Every
line-initial `theorem`/`lemma` in the six modules was scripted
into the drivers (208/208 resolved; an ASCII-only name regex
initially truncated 5 `Γ`-suffixed ProductTriple names and missed
2 `π`- and 3 `η`-initial names — caught, re-run in a supplementary
driver, all bucket (a); three prime-suffixed names —
`eps''_prod`, `hsign'C`, `gradProj_mul_orth'` — verified directly
from driver output, all bucket (a)). Wall-clock: FiniteSpectralTriple
164 s (slow olean IO, as the pack warned — it imports Scaffold32,
not DiracTorsionMap/EdgeSignature; no workaround was needed beyond
patience), all other modules 5–13 s each. Drivers and raw outputs
retained at `/tmp/audit-drivers/*.lean` / `*.out`.

## Task 1 — fresh axiom footprints (all 208 headlines)

Bucket (a) = footprint ⊆ {propext, Classical.choice, Quot.sound}.
Bucket (b) = corpus T2/T4 file axioms, named in the last column.
Bucket (c) = sorryAx — **zero occurrences in the family**.

### FiniteSpectralTriple

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| piOp_def_check | 77 | (a) | — |
| pi_zero_of_ge_16 | 80 | (a) | — |
| pi_pure_color_zero | 93 | (a) | — |
| piOp_zero_of_lt_16 | 102 | (a) | — |
| order_zero_condition | 118 | (a) | — |
| buildDirac_Bdag_entry | 164 | (a) | — |
| buildDirac_Edag_entry | 174 | (a) | — |
| buildDirac_B_entry | 184 | (a) | — |
| gammaF_mul_apply | 193 | (a) | — |
| mul_gammaF_apply | 201 | (a) | — |
| buildDirac_nonzero_opp_grading | 211 | (a) | — |
| buildDirac_gamma_odd | 278 | (a) | — |
| buildDirac_self_adjoint | 289 | (a) | — |
| buildDirac_J_compat | 335 | (a) | — |

### ConcreteBoundedTriple

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| pauliD_sub_smul_matrix | 57 | (a) | — |
| pauliD_sub_det | 64 | (a) | — |
| pauliD_resolvent | 77 | (a) | — |
| pauliD_resolvent_compact | 108 | (a) | — |

### BoundedTriple

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| nrm_comp_bound | 153 | (a) | — |
| bounded_nrm_triangle | 171 | (a) | — |
| Dprod_sq_analytic | 208 | (a) | — |
| prod_commutator_decomp_analytic | 224 | (a) | — |
| prod_commutator_tmul_analytic | 242 | (a) | — |
| prod_commutator_factorBounds | 261 | (a) | — |

### AnalyticTriple

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| iprod_add_left | 96 | (a) | — |
| iprod_add_right | 101 | (a) | — |
| iprod_smul_left | 107 | (a) | — |
| iprod_smul_right | 113 | (a) | — |
| iprod_sub_left | 118 | (a) | — |
| iprod_sub_right | 123 | (a) | — |
| iprod_zero_right | 128 | (a) | — |
| star_mul_self | 141 | (a) | — |
| star_re | 147 | (a) | — |
| re_le_norm | 153 | (a) | — |
| iprod_re_nonneg | 158 | (a) | — |
| iprod_symm | 170 | (a) | — |
| iprod_eta | 177 | (a) | — |
| cauchy_schwarz | 198 | (a) | — |
| nrm_smul | 256 | (a) | — |
| nrm_eq_zero | 270 | (a) | — |
| nrm_triangle | 287 | (a) | — |

### ProductTriple

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| koM_valid | 249 | (a) | — |
| koF_valid | 255 | (a) | — |
| opTensor_mul | 272 | (a) | — |
| opTensor_one | 280 | (a) | — |
| opTensor_add_left | 287 | (a) | — |
| opTensor_add_right | 295 | (a) | — |
| opTensor_smul_left | 303 | (a) | — |
| opTensor_smul_right | 311 | (a) | — |
| opTensor_zero_left | 319 | (a) | — |
| opTensor_zero_right | 326 | (a) | — |
| opTensor_neg_left | 333 | (a) | — |
| opTensor_neg_right | 341 | (a) | — |
| opTensor_sub_left | 349 | (a) | — |
| opTensor_sub_right | 356 | (a) | — |
| Gprod_sq | 388 | (a) | — |
| Dprod_odd | 394 | (a) | — |
| Dprod_sq | 409 | (a) | — |
| πprod_even | 422 | (a) | — |
| πprodLin_tmul | 457 | (a) | — |
| flipProd_involutive | 505 | (a) | — |
| flipProd_CM_regular | 516 | (a) | — |
| prodFlip_CM_regular | 526 | (a) | — |
| Gproj_add | 542 | (a) | — |
| prodTwist_diag_is_ordinary | 569 | (a) | — |
| prodTwist_factorform | 584 | (a) | — |
| prodTwist_general_pair | 592 | (a) | — |
| prod_commutator_decomp | 645 | (a) | — |
| prod_commutator_pureManifold | 659 | (a) | — |
| prod_commutator_pureFinite | 669 | (a) | — |
| koProd_signs | 701 | (a) | — |
| koDim_add | 708 | (a) | — |
| conjJprodElem_tmul | 741 | (a) | — |
| conjJprodElem_mul | 751 | (a) | — |
| conjJprod_D | 762 | (a) | — |
| conjJprod_Γ | 783 | (a) | — |
| Jprod_tmul | 820 | (a) | — |
| Dprod_tmul | 825 | (a) | — |
| Gprod_tmul | 833 | (a) | — |
| Janti_sq_M | 840 | (a) | — |
| Janti_sq_F | 846 | (a) | — |
| Janti_D_M | 852 | (a) | — |
| Janti_Γ_M | 859 | (a) | — |
| Janti_D_F | 866 | (a) | — |
| Janti_Γ_F | 873 | (a) | — |
| eps_prod | 880 | (a) | — |
| eps''_prod | 886 | (a) | — |
| hsignC | 892 | (a) | — |
| hsign'C | 898 | (a) | — |
| Jprod_sq | 905 | (a) | — |
| Jprod_D | 916 | (a) | — |
| Jprod_Γ | 931 | (a) | — |
| Jprod_comp_sq | 942 | (a) | — |
| Jprod_comp_D | 948 | (a) | — |
| Jprod_comp_Γ | 954 | (a) | — |
| sesqProd_tmul | 1004 | (a) | — |
| ηprod_tmul | 1021 | (a) | — |
| ηprod_sq | 1027 | (a) | — |
| ηprod_selfadj | 1035 | (a) | — |
| oppProd_tmul | 1102 | (a) | — |
| oppProd_anti_tmul | 1113 | (a) | — |
| oppgrandProd_flip | 1131 | (a) | — |
| oppgrandProd_diag | 1139 | (a) | — |
| prodTwistedFOC_diag_reduce | 1163 | (a) | — |

### TwistedTriple

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| twisted_leibniz | 181 | (a) | — |
| twisted_add | 190 | (a) | — |
| twisted_one | 199 | (a) | — |
| twistedComm_id_is_comm | 206 | (a) | — |
| twistConj_mul | 221 | (a) | — |
| twistConj_comp | 234 | (a) | — |
| twistConj_one | 241 | (a) | — |
| twistConj_one_eq_id | 246 | (a) | — |
| twistedComm_twistConj_one | 251 | (a) | — |
| twistConj_inv_left | 257 | (a) | — |
| twistConj_inv_right | 268 | (a) | — |
| twistConj_star | 298 | (a) | — |
| twistConj_CM_iff_centralSq | 311 | (a) | — |
| twistConj_CM_of_involutive | 350 | (a) | — |
| twistConjAuto_CM_iff | 366 | (a) | — |
| twistedComm_flow_zero | 379 | (a) | — |
| modularTwist_zero | 394 | (a) | — |
| bimod_mul_left | 420 | (a) | — |
| bimod_add_left | 426 | (a) | — |
| bimod_lr_compat | 435 | (a) | — |
| twistedComm_mem_oneForm | 448 | (a) | — |
| twistedOneForm_zero | 454 | (a) | — |
| twistedOneForm_add | 459 | (a) | — |
| twistedOneForm_twistL | 471 | (a) | — |
| twistedOneForm_mul_right | 486 | (a) | — |
| twistedComm_mem_subalgebra | 521 | (a) | — |
| twistedFluctuation_selfAdjoint | 560 | (a) | — |
| gradProj_add | 586 | (a) | — |
| gradProj_mul_orth | 598 | (a) | — |
| gradProj_mul_orth' | 609 | (a) | — |
| gradProjPlus_sq | 620 | (a) | — |
| gradProjMinus_sq | 640 | (a) | — |
| gradProjPlus_hermitian | 660 | (a) | — |
| gradProjMinus_hermitian | 669 | (a) | — |
| even_mul | 679 | (a) | — |
| gradProjPlus_comm_of_comm | 690 | (a) | — |
| gradProjMinus_comm_of_comm | 698 | (a) | — |
| flipTwist_involutive | 714 | (a) | — |
| flipTwist_mul | 720 | (a) | — |
| flipTwist_add | 727 | (a) | — |
| flipTwist_one | 734 | (a) | — |
| flipTwist_CM_regular | 745 | (a) | — |
| twistByGrading_trivial | 756 | (a) | — |
| grandRep_add | 771 | (a) | — |
| grandRep_mul_of_comm | 789 | (a) | — |
| twistedCommGrand_add | 885 | (a) | — |
| twistedCommGrand_leibniz | 900 | (a) | — |
| twistedCommGrand_diag | 928 | (a) | — |
| kreinAdjoint_involutive | 1034 | (a) | — |
| swapR_sq | 1049 | (a) | — |
| swapR_hermitian | 1057 | (a) | — |
| swapR_fundamental | 1063 | (a) | — |
| swapR_conj_blockDiag | 1069 | (a) | — |
| kreinSymm_blockDiag_of_selfAdjoint | 1083 | (a) | — |
| kreinSymm_blockDiag_iff_selfAdjoint | 1092 | (a) | — |
| kreinSymm_twistedFluctuation_iff | 1109 | (a) | — |
| swapR_implements_flip | 1121 | (a) | — |
| trace_swapR | 1132 | (a) | — |
| kreinSymm_swapR_transport_of_comm | 1156 | (a) | — |
| kreinSymm_swapR_transport_of_anticomm | 1185 | (a) | — |
| kreinProd_one | 1218 | (a) | — |
| kreinProd_fundSymm_self | 1226 | (a) | — |
| swapR_ne_diagGrading | 1239 | (a) | — |
| swapR_kreinUnitary_self | 1253 | (a) | — |
| kreinSymm_add | 1375 | (a) | — |
| kreinSymm_sub | 1385 | (a) | — |
| kreinSymm_real_smul | 1396 | (a) | — |
| rhoReal_blockDiag_iff | 1410 | (a) | — |
| kreinSymm_fluctuation_of_rhoReal | 1431 | (a) | — |
| rhoReal_of_kreinSymm_fluctuation | 1452 | (a) | — |
| kreinSymm_fluctuation_iff_rhoReal | 1475 | (a) | — |
| causalLE_refl | 1605 | (a) | — |
| causalLE_trans | 1613 | (a) | — |
| re_sum_helper | 1623 | (a) | — |
| form_single_eq | 1632 | (a) | — |
| re_form_one | 1642 | (a) | — |
| isPosSemidef_zero | 1656 | (a) | — |
| isPosSemidef_add | 1662 | (a) | — |
| isPosSemidef_real_smul | 1671 | (a) | — |
| isPosSemidef_one | 1684 | (a) | — |
| form_affine | 1691 | (a) | — |
| posSemidef_trace_eq_zero | 1715 | (a) | — |
| trace_comm_eq_zero | 1794 | (a) | — |
| dyn_comm_eq_zero | 1801 | (a) | — |
| causalCone_forces_central | 1819 | (a) | — |
| causalCone_obstruction | 1848 | (a) | — |
| selfAdjointSet_static | 1860 | (a) | — |
| norm_mul_le_sum_sq | 1876 | (a) | — |
| estimate_aux | 1893 | (a) | — |
| isPosSemidef_shift_add | 1938 | (a) | — |
| isPosSemidef_shift_sub | 1964 | (a) | — |
| psd_spanning | 1983 | (a) | — |
| psdCone_static | 2009 | (a) | — |

### CCMAlgebraClassification

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| smFactors_dim_ok | 86 | (a) | — |
| smFactors_faithful | 89 | (a) | — |
| smFactors_orientable | 92 | (a) | — |
| filters_do_not_classify | 107 | (a) | — |
| minimalBlock_sum | 143 | (a) | — |
| singlet_remainder | 146 | (a) | — |
| ccm_classification | 225 | (b) | AdmitsClassifyingDirac_unpack, exoticBasisAux, exotic_decomposition |

### CFKernelClassification

| headline | line | bucket | axioms beyond standard three |
|---|---|---|---|
| smSector_mem_nullspace | 51 | (a) | — |
| exotic_coefficients_zero | 139 | (a) | — |
| cf_kernel_classification_46_10 | 189 | (b) | exoticBasisAux, exotic_decomposition |
| cf_kernel_classification_full | 238 | (b) | exoticBasisAux, exotic_decomposition |

---

## Task 2 — statement substance (OSReconstruction standard)

Verdict key: **NON-DEGENERATE** = the triple's data (algebra,
Hilbert/spinor space, Dirac, grading/real structure where claimed)
is actually constrained by the hypotheses and inputs are tied to
outputs. For class-based modules the hypotheses include the T2
class fields — the verdict is then "non-degenerate *relative to
the stated class data*", and the level caveat of §1 applies.
**WEAK** and **TRIVIAL** as defined in the verdict paragraph.

### FiniteSpectralTriple.lean (527 lines; all 14 bucket (a))

Definition-level note (not a theorem): `SMAlgebra`
(FiniteSpectralTriple.lean:22–25) is a bare component bundle
`u1 : ℂ`, `q : Matrix I2 I2 ℂ`, `color : Matrix I3 I3 ℂ` — no
algebra operations are defined on it in this file, and `q` is an
unconstrained 2×2 complex matrix (the "ℍ" reading is the T2
naming in the docstring, FiniteSpectralTriple.lean:21, not a
constructed quaternion algebra). All theorems below are matrix
statements about `embedSM`/`pi`/`buildDirac` and are unaffected.

- `piOp_def_check` (:77) — asserts `piOp a` equals its own defining
  expression. **TRIVIAL** (`rfl`; docstring labels it "Definitional
  regression guard", :76).
- `pi_zero_of_ge_16` (:80) — `pi a` entries vanish outside the
  16×16 particle block. NON-DEGENERATE.
- `pi_pure_color_zero` (:93) — a pure-color element `⟨0,0,m⟩` acts
  as 0 under `pi` (structural consequence of `embedSM`'s block
  form). NON-DEGENERATE.
- `piOp_zero_of_lt_16` (:102) — opposite representation entries
  vanish inside the particle block (support disjointness).
  NON-DEGENERATE.
- `order_zero_condition` (:118) — **[π(a), π°(b)] = 0 for all
  a, b** — the order-zero axiom of the finite triple, proved from
  the disjoint supports. Headline. NON-DEGENERATE.
- `buildDirac_Bdag_entry` (:164), `buildDirac_Edag_entry` (:174),
  `buildDirac_B_entry` (:184) — entry identifications of the
  four-block Dirac in the B†/E†/B regions under index hypotheses.
  NON-DEGENERATE (definitional unfolding, hypotheses used).
- `gammaF_mul_apply` (:193), `mul_gammaF_apply` (:201) —
  entrywise action of the diagonal grading γ_F. NON-DEGENERATE.
- `buildDirac_nonzero_opp_grading` (:211) — every nonzero entry of
  `buildDirac A B C E` connects opposite γ_F eigenspaces.
  NON-DEGENERATE.
- `buildDirac_gamma_odd` (:278) — **{γ_F, D} = 0** for all block
  parameters A B C E. Headline. NON-DEGENERATE.
- `buildDirac_self_adjoint` (:289) — **D† = D** for all block
  parameters. Headline. NON-DEGENERATE.
- `buildDirac_J_compat` (:335) — **J-compatibility**
  `UJ * D.map star * UJ = D`, conditional on the block symmetries
  `hB : B = A.map star`, `hC : C = C.transpose`,
  `hE : E = E.transpose` — all three hypotheses are used.
  Headline. NON-DEGENERATE.

### ConcreteBoundedTriple.lean (159 lines; 4 theorems bucket (a), 1 instance bucket (b))

- `pauliD_sub_smul_matrix` (:57) — the matrix of `pauliD − λ•1`
  under `endAlgEquiv` is `pauliX − λ•1`. NON-DEGENERATE.
- `pauliD_sub_det` (:64) — `det (pauliX − λ•1) = λ² − 1` by direct
  2×2 computation. NON-DEGENERATE.
- `pauliD_resolvent` (:77) — **for λ ∉ {1, −1} the resolvent
  exists as a two-sided inverse**. NON-DEGENERATE.
- `pauliD_resolvent_compact` (:108) — the same resolvent is a
  compact operator (finite-dimensionality, `end_compact`).
  NON-DEGENERATE.
- `pauliBounded` (instance, :142) — the `BoundedAnalyticTriple`
  instance for the Pauli model: `hbddComm`/`hbddRep` are the proved
  T1s of ConcreteFiniteModel; `hcompactRes` is discharged by the
  labeled T2 axiom `pauli_compactResolvent` (:131) whose content
  is the two theorems above. CONDITIONAL (bucket b), disclosed
  in-file (:26–42). Substance caveat, also disclosed in-file
  (:38–42): the model is analytically trivial — scalar π makes
  all commutators vanish (`bddComm` with C = 0) — so the instance
  discharges analytic debt, not gauge content.

### BoundedTriple.lean (292 lines; all 6 bucket (a))

Level note: `BoundedAnalyticTriple` (BoundedTriple.lean:102–122)
is a class extending `AnalyticTripleData` with fields
`hbddComm` (bounded commutators), `hbddRep` (bounded
representation), `hcompactRes : HasCompactResolvent D`, where
`HasCompactResolvent` is an **opaque** Prop (BoundedTriple.lean:88–89).
The header states plainly: "`hcompactRes` is carried, never used:
no theorem below depends on it" (BoundedTriple.lean:65) — verified:
all six footprints are standard-only, and no theorem's statement
mentions `HasCompactResolvent`. The full product estimate
`‖[DprodB, πprodB (f⊗a)] z‖ ≤ K‖z‖` is explicitly NOT proved
(no tensor-product norm; BoundedTriple.lean:48–60, 283–285).

- `nrm_comp_bound` (:153) — pointwise `nrm` bounds compose
  multiplicatively (uses all bound hypotheses incl. `0 ≤ C₁`).
  NON-DEGENERATE.
- `bounded_nrm_triangle` (:171) — the AnalyticTriple triangle
  inequality applies definitionally to bounded data.
  NON-DEGENERATE (one-line re-application, labeled as such, :168–170).
- `Dprod_sq_analytic` (:208) — **DprodB² = D_M² ⊗ 1 + 1 ⊗ D_F²**
  on enriched factors (cross terms killed by `hΓD`). NON-DEGENERATE.
- `prod_commutator_decomp_analytic` (:224) — **[DprodB, πprodB f a]
  decomposition** into manifold/finite 1-form summands.
  NON-DEGENERATE.
- `prod_commutator_tmul_analytic` (:242) — the decomposition
  evaluated on elementary tensors `x ⊗ₜ y`. NON-DEGENERATE.
- `prod_commutator_factorBounds` (:261) — existence of the three
  factor-component bound constants. REPACKAGING (not counted
  weak): the conclusion is exactly the class fields `hbddComm` /
  `hbddRep` applied to the given `f, a` — the docstring says
  "packaged" (BoundedTriple.lean:253–260) and pins what it does
  not give (no norm on `x ⊗ₜ y`, no bound for `Γ_M`). Inputs are
  tied to outputs; nothing stronger is claimed.

### AnalyticTriple.lean (329 lines; all 17 bucket (a))

Level note: positivity/definiteness are T2 class fields of
`AnalyticTripleData` (`hiprod_pos`, `hiprod_def`,
AnalyticTriple.lean:75–77), disclosed in the header
(AnalyticTriple.lean:29–35): they "cannot be proved from
nothing — they are properties, not theorems", dischargeable by a
concrete model. The theorems are non-degenerate *given that data*:
each uses the fields it needs.

- Sesquilinearity sextet — `iprod_add_left` (:96),
  `iprod_add_right` (:101), `iprod_smul_left` (:107),
  `iprod_smul_right` (:113), `iprod_sub_left` (:118),
  `iprod_sub_right` (:123), plus `iprod_zero_right` (:128):
  `iprod x y = sesq (ηsym x) y` is antilinear in x, linear in y,
  from `sesq`'s semilinearity and `ηsym`'s linearity.
  NON-DEGENERATE.
- ℂ helpers — `star_mul_self` (:141), `star_re` (:147),
  `re_le_norm` (:153). NON-DEGENERATE.
- `iprod_re_nonneg` (:158) — `0 ≤ (iprod x x).re`, from
  `hiprod_pos`. NON-DEGENERATE.
- `iprod_symm` (:170) — conjugate symmetry of `iprod`, via
  `hsesq_symm` + `hηsym_selfadj`. NON-DEGENERATE.
- `iprod_eta` (:177) — `iprod` invariant under `ηsym` in both
  arguments, via `hηsym_sq`. NON-DEGENERATE.
- `cauchy_schwarz` (:198) — **‖iprod x y‖² ≤ (iprod x x).re ·
  (iprod y y).re**, proved from `hiprod_pos` + `hiprod_def` +
  sesquilinearity. Headline. NON-DEGENERATE.
- `nrm_smul` (:256), `nrm_eq_zero` (:270), `nrm_triangle` (:287)
  — the norm `nrm x = √((iprod x x).re)` is homogeneous, definite
  (uses `hiprod_def`), and subadditive (via Cauchy–Schwarz).
  NON-DEGENERATE. (Completeness is pinned, not claimed:
  AnalyticTriple.lean:322.)

### ProductTriple.lean (1283 lines; all 63 bucket (a))

Level note: `TripleData` (ProductTriple.lean:167–197) is a T2
class packaging algebra A, spinor module S, representation π,
Dirac D, grading Γ, the linear real-structure shadow `conjJ`,
the antilinear `Janti` with KO relations as fields, a sesquilinear
form `sesq`, and the fundamental symmetry `ηsym`.
`ManifoldFactor` (ProductTriple.lean:202–205) adds KO-dim-4 signs
and a commutative algebra; `FiniteFactor` (ProductTriple.lean:212–213)
adds KO-dim-6 signs. The header is explicit: "M itself is never
constructed… NO continuum is constructed: no manifold, no spin
geometry, no elliptic analysis, no Hilbert inner product"
(ProductTriple.lean:30–38, 198–201). No instance of either factor
class is constructed in this module. Every theorem below is a
consequence of those class fields, and the fields are actually
used (`hΓsq`, `hΓD`, `hπeven`, `hconjJ_*`, `hJanti_*`,
`hηsym_*`, `ko4`, `ko6`).

- `koM_valid` (:249), `koF_valid` (:255) — the manifold/finite KO
  sign triples are ±1-valid, from `ko4`/`ko6`. NON-DEGENERATE (small).
- opTensor toolkit (12) — `opTensor_mul` (:272), `opTensor_one`
  (:280), `opTensor_add_left` (:287), `opTensor_add_right` (:295),
  `opTensor_smul_left` (:303), `opTensor_smul_right` (:311),
  `opTensor_zero_left` (:319), `opTensor_zero_right` (:326),
  `opTensor_neg_left` (:333), `opTensor_neg_right` (:341),
  `opTensor_sub_left` (:349), `opTensor_sub_right` (:356): the
  operator tensor product `TensorProduct.map` obeys the
  mixed-product, unit, additivity, homogeneity, zero, negation,
  subtraction laws. NON-DEGENERATE toolkit.
- `Gprod_sq` (:388) — **Gprod² = 1**. `Dprod_odd` (:394) —
  **Dprod anticommutes with Gprod**. `Dprod_sq` (:409) —
  **Dprod² = D_M² ⊗ 1 + 1 ⊗ D_F²** (sum of squares; cross terms
  killed by `hΓD`). `πprod_even` (:422) — the product
  representation is grading-even (uses `hπeven` of both factors).
  `πprodLin_tmul` (:457) — `πprodLin` on elementary tensors.
  Headlines. NON-DEGENERATE.
- `flipProd_involutive` (:505), `flipProd_CM_regular` (:516),
  `prodFlip_CM_regular` (:526) — the flip on the doubled product
  algebra is involutive and commutes with `star` componentwise
  (CM-regularity for the flip). **TRIVIAL-but-exact** (`rfl`, empty
  footprint for the first two): for the flip, CM-regularity *is*
  this componentwise equation, and the docstring says
  "UNCONDITIONAL" with the one-line reason (ProductTriple.lean:511–515).
- `Gproj_add` (:542) — the grading projectors sum to 1 (any Γ).
  NON-DEGENERATE (small).
- `prodTwist_diag_is_ordinary` (:569) — on diagonal pairs the
  flip-twisted commutator IS the ordinary commutator
  (uses `Gproj_add`). NON-DEGENERATE.
- `prodTwist_factorform` (:584), `prodTwist_general_pair` (:592)
  — the flip on (shared-factor) elementary pairs is `id_M ⊗ flip_F`,
  resp. swaps general pairs. **TRIVIAL** (`rfl`; docstrings state
  "By `rfl` — definitional", ProductTriple.lean:581, 590).
- `prod_commutator_decomp` (:645) — **[Dprod, πprod f a] =
  [D_M,π_M f] ⊗ π_F(a) + (π_M(f)Γ_M) ⊗ [D_F,π_F a]** — the
  inner-fluctuation decomposition (gauge fields + scalars).
  Headline. NON-DEGENERATE.
- `prod_commutator_pureManifold` (:659),
  `prod_commutator_pureFinite` (:669) — the two summands isolated
  at `a = 1` / `f = 1`. NON-DEGENERATE corollaries.
- `koProd_signs` (:701) — product KO signs are the KO-dim-2 row
  (−1,+1,−1), from `ko4`/`ko6`. NON-DEGENERATE (small).
  `koDim_add` (:708) — `(4+6) % 8 = 2`. **TRIVIAL** (`rfl`).
- conjJ shadow — `conjJprodElem_tmul` (:741),
  `conjJprodElem_mul` (:751), `conjJprod_D` (:762),
  `conjJprod_Γ` (:783): the factored `conjJ` anti-automorphism
  acts factorwise and obeys the ε′/ε″ relations on Dprod/Gprod.
  NON-DEGENERATE.
- Antilinear J product — `Jprod_tmul` (:820), `Janti_sq_M` (:840),
  `Janti_sq_F` (:846), `Janti_D_M` (:852), `Janti_Γ_M` (:859),
  `Janti_D_F` (:866), `Janti_Γ_F` (:873), `eps_prod` (:880),
  `eps''_prod` (:886), `hsignC` (:892), `hsign'C` (:898),
  `Jprod_sq` (:905) (**J_prod² = −1** on tensors), `Jprod_D`
  (:916) (**J_prod Dprod = Dprod J_prod**), `Jprod_Γ` (:931)
  (**J_prod Γ_prod = −Γ_prod J_prod**), `Jprod_comp_sq` (:942),
  `Jprod_comp_D` (:948), `Jprod_comp_Γ` (:954) (the same three as
  operator compositions): all derived from the factor `hJanti_*`
  fields and the multiplied KO signs. Headlines NON-DEGENERATE;
  the `eps_*`/`hsign*` four are their sign-arithmetic components.
- Krein product — `sesqProd_tmul` (:1004) (product form factors on
  elementary tensors), `ηprod_tmul` (:1021), `ηprod_sq` (:1027)
  (**η_prod² = 1**), `ηprod_selfadj` (:1035) (η_prod self-adjoint
  for the product form). NON-DEGENERATE.
- Opposite representation — `oppProd_tmul` (:1102),
  `oppProd_anti_tmul` (:1113) (oppProd reverses multiplication on
  elementary tensors, via `hconjJ_mul`), `oppgrandProd_flip`
  (:1131) (**TRIVIAL**, `rfl`: flip-compatibility in statable
  form), `oppgrandProd_diag` (:1139), and
  `prodTwistedFOC_diag_reduce` (:1163) — the twisted first-order
  condition on diagonal pairs is *equivalent* to the ordinary
  product FOC (`ProdFirstOrderCond`, a stated Prop, not proved —
  pinned on factor-level order-one, ProductTriple.lean:1152–1161).
  NON-DEGENERATE except as noted.

### TwistedTriple.lean (2044 lines; all 93 bucket (a))

Level note: everything is finite matrix algebra over
`Matrix n n ℂ`. A twist is explicit data (`TwistAuto`,
TwistedTriple.lean:159–168: multiplicativity, additivity,
`ρ(1) = 1`, two-sided inverse as fields). Pinned Prop defs
(`TwistedFirstOrderCond` :537, `TwistedFirstOrderCondGrand`
:948, `AntilinearJCompat` :1265, `KreinUnitaryTwist` :1278) are
*stated, not claimed* — no theorem asserts them.

- Twisted commutator calculus — `twisted_leibniz` (:181),
  `twisted_add` (:190), `twisted_one` (:199),
  `twistedComm_id_is_comm` (:206): `[D,·]_ρ` obeys the twisted
  Leibniz rule etc. from the `TwistAuto` fields. NON-DEGENERATE.
- Inner twist — `twistConj_mul` (:221), `twistConj_comp` (:234),
  `twistConj_one` (:241), `twistConj_one_eq_id` (:246),
  `twistedComm_twistConj_one` (:251), `twistConj_inv_left`
  (:257), `twistConj_inv_right` (:268), `twistConj_star` (:298)
  (ρ_U is a *-automorphism, unconditional), and the CM-regularity
  characterization `twistConj_CM_iff_centralSq` (:311) —
  **CM-regularity for ρ_U ⟺ U² is central** — with
  `twistConj_CM_of_involutive` (:350) and
  `twistConjAuto_CM_iff` (:366). Headlines. NON-DEGENERATE.
  (The file's header records the numerical *refutation* of
  unconditional CM-regularity for ρ_U, TwistedTriple.lean:36–44.)
- s→0 limit — `twistedComm_flow_zero` (:379),
  `modularTwist_zero` (:394): at s = 0 the (modular) twist is the
  identity and the twisted commutator is the ordinary commutator.
  NON-DEGENERATE.
- Bimodule/1-forms — `bimod_mul_left` (:420), `bimod_add_left`
  (:426): NON-DEGENERATE (small). `bimod_lr_compat` (:435) —
  **TRIVIAL**: the statement is exactly `Matrix.mul_assoc`
  (proof is the term `Matrix.mul_assoc _ _ _`, :438–439).
  `twistedComm_mem_oneForm` (:448), `twistedOneForm_zero` (:454),
  `twistedOneForm_add` (:459), `twistedOneForm_twistL` (:471),
  `twistedOneForm_mul_right` (:486): twisted 1-forms contain the
  twisted commutators and are closed under +, left twist action,
  right multiplication. NON-DEGENERATE.
- `twistedComm_mem_subalgebra` (:521) — conditional: preserved
  subalgebra + D ∈ S ⟹ twisted commutators stay in S (hypotheses
  used; preservation is *not* assumed automatic — header records
  its numerical refutation for the modular flow, :46–51).
  NON-DEGENERATE.
- `twistedFluctuation_selfAdjoint` (:560) — the twisted
  fluctuation is self-adjoint *given* D, A_ρ self-adjoint and ε₁
  real (hypotheses used; the 1-form's own self-adjointness stays
  pinned). NON-DEGENERATE.
- §7 flip/grand — projector algebra: `gradProj_add` (:586),
  `gradProj_mul_orth` (:598), `gradProj_mul_orth'` (:609),
  `gradProjPlus_sq` (:620), `gradProjMinus_sq` (:640),
  `gradProjPlus_hermitian` (:660), `gradProjMinus_hermitian`
  (:669), `even_mul` (:679), `gradProjPlus_comm_of_comm` (:690),
  `gradProjMinus_comm_of_comm` (:698) — under `Γ² = 1` / `Γᴴ = Γ`
  hypotheses where needed. NON-DEGENERATE. Flip group:
  `flipTwist_involutive` (:714), `flipTwist_mul` (:720),
  `flipTwist_add` (:727), `flipTwist_one` (:734),
  `flipTwist_CM_regular` (:745) — **TRIVIAL-but-exact** (`rfl`
  after case split; as with ProductTriple, CM-regularity for the
  flip is this componentwise equation). `twistByGrading_trivial`
  (:756) — on graded elements Γ-conjugation is trivial
  (`ΓaΓ = a` from `Γ² = 1` + commutation; both hypotheses used) —
  a proved *triviality result*, not a trivial proof. NON-DEGENERATE.
  `grandRep_add` (:771), `grandRep_mul_of_comm` (:789)
  (multiplicativity conditional on evenness), 
  `twistedCommGrand_add` (:885), `twistedCommGrand_leibniz`
  (:900), `twistedCommGrand_diag` (:928) (diagonal pairs give the
  ordinary commutator). NON-DEGENERATE.
- §8 Krein/swap — `kreinAdjoint_involutive` (:1034) (Krein adjoint
  is an involution, from `η² = 1`, `ηᴴ = η`), `swapR_sq` (:1049),
  `swapR_hermitian` (:1057), `swapR_fundamental` (:1063),
  `swapR_conj_blockDiag` (:1069),
  `kreinSymm_blockDiag_of_selfAdjoint` (:1083),
  `kreinSymm_blockDiag_iff_selfAdjoint` (:1092) (**doubled
  block-diagonal Krein symmetry ⟺ self-adjointness**),
  `kreinSymm_twistedFluctuation_iff` (:1109) (the same iff for
  the doubled fluctuation — a one-step application of the
  previous iff, labeled conditional), `swapR_implements_flip`
  (:1121), `trace_swapR` (:1132),
  `kreinSymm_swapR_transport_of_comm` (:1156),
  `kreinSymm_swapR_transport_of_anticomm` (:1185) (linear
  stand-ins, antilinear case pinned), `kreinProd_one` (:1218),
  `kreinProd_fundSymm_self` (:1226), `swapR_ne_diagGrading`
  (:1239) (**R ≠ Γ**, needs `[Nonempty n]`), 
  `swapR_kreinUnitary_self` (:1253). NON-DEGENERATE.
- §9 reality — `kreinSymm_add` (:1375), `kreinSymm_sub` (:1385),
  `kreinSymm_real_smul` (:1396), `rhoReal_blockDiag_iff` (:1410)
  (**ρ-reality of the doubled 1-form ⟺ A' = Aᴴ**),
  `kreinSymm_fluctuation_of_rhoReal` (:1431),
  `rhoReal_of_kreinSymm_fluctuation` (:1452),
  `kreinSymm_fluctuation_iff_rhoReal` (:1475) — the conditional
  iff, under `Dᴴ = D`, packaged J-term ρ-reality, ε₁ real.
  NON-DEGENERATE. (In `rhoReal_of_kreinSymm_fluctuation` the
  hypothesis `_hA'` is deliberately unused — underscore-named and
  disclosed in its docstring, TwistedTriple.lean:1445–1451;
  keeping one hypothesis set for both directions. Not counted weak.)
- §10 causal cones — helpers `causalLE_refl` (:1605),
  `causalLE_trans` (:1613), `re_sum_helper` (:1623),
  `form_single_eq` (:1632), `re_form_one` (:1642),
  `form_affine` (:1691), `norm_mul_le_sum_sq` (:1876),
  `estimate_aux` (:1893); PSD algebra `isPosSemidef_zero` (:1656),
  `isPosSemidef_add` (:1662), `isPosSemidef_real_smul` (:1671),
  `isPosSemidef_one` (:1684), `isPosSemidef_shift_add` (:1938),
  `isPosSemidef_shift_sub` (:1964), `psd_spanning` (:1983)
  (every self-adjoint M is a difference of two PSD matrices);
  the engine `posSemidef_trace_eq_zero` (:1715) (PSD + trace 0
  ⟹ = 0, via polarization), `trace_comm_eq_zero` (:1794),
  `dyn_comm_eq_zero` (:1801) (dynamical axiom ⟹ [D,f] = 0 —
  trace-class collapse), `causalCone_forces_central` (:1819),
  **`causalCone_obstruction` (:1848) — the section's verdict:
  static Franco axioms + i[D,f]-PSD dynamical compatibility +
  self-adjoint non-central D ⟹ False**, `selfAdjointSet_static`
  (:1860), `psdCone_static` (:2009) (the PSD cone does satisfy
  the static axioms — the Löwner order). All NON-DEGENERATE.
  Scope honesty in-file: `IsCausalConeStatic` weakens Franco's
  (F4) to `1 ∈ C` (TwistedTriple.lean:1561–1577, obstruction
  applies a fortiori), and the obstruction kills the i[D,f]-PSD
  variant, NOT Franco's true J-form (F6), whose finite verdict
  stays open (`IsLorentzCompatible`, stated, no verdict).

### CCMAlgebraClassification.lean (238 lines; 6 bucket (a), 1 bucket (b))

- `smFactors_dim_ok` (:86), `smFactors_faithful` (:89),
  `smFactors_orientable` (:92) — the SM factor list passes the
  dimension (16), faithfulness, orientability filters, by
  `decide` (empty footprints). NON-DEGENERATE as finite checks
  (small).
- `filters_do_not_classify` (:107) — **a distinct explicit factor
  list (`altFactors`) passes all three algebra-side filters**:
  the filters provably do not classify. The file's substantive
  negative headline. NON-DEGENERATE (empty footprint).
- `minimalBlock_sum` (:143), `singlet_remainder` (:146) —
  multiplicity arithmetic (12, remainder 4), by `decide`.
  NON-DEGENERATE (small; the header, :124–135, states the Lean
  content is the arithmetic and the block-inventory reading is T4).
- `ccm_classification` (:225) — **WEAK (W1) + CONDITIONAL** —
  see the verdict section. Its own header flags it UNSOUND AS
  STATED via the CF chain (CCMAlgebraClassification.lean:225–232).

### CFKernelClassification.lean (250 lines; 2 bucket (a), 2 bucket (b))

- `smSector_mem_nullspace` (:51) — every `smDirac` lies in the
  order-one nullspace (via `OrderOneHolds_smDirac`). Bucket (a).
  NON-DEGENERATE.
- `exotic_coefficients_zero` (:139) — an invertible pivot matrix
  kills all exotic coefficients (linear algebra; `h_det` used).
  Bucket (a). NON-DEGENERATE — note this is the *elimination
  logic*; the existence of the decomposition + pivot matrix is
  the axiom's job, not this theorem's.
- `cf_kernel_classification_46_10` (:189) — order-one +
  `[D, C_F] = 0` ⟹ D in the SM physical sector. CONDITIONAL on
  `exotic_decomposition` + `exoticBasisAux` (bucket b), and the
  consumed axiom is flagged FALSE AS STATED in its own docstring
  (:122–131) — so this headline's *statement* is, per the corpus's
  own flag, false as stated in the weak-predicate domain; it
  stands unmodified under the relabeling rule, with the corrected
  classification in `CFKernelRetarget` (outside audit scope).
  As a derivation it is non-degenerate (both hypotheses used;
  conclusion is exactly the sector membership).
- `cf_kernel_classification_full` (:238) — **WEAK (W2) +
  CONDITIONAL** — see the verdict section.

## 5.3 Trivial-but-exact headlines (not counted weak)

Proof by `rfl`/`decide`, footprint empty or standard, each
labeled definitional in its own docstring:
`FiniteSpectralTriple.piOp_def_check` (:77, regression guard);
`ProductTriple.prodTwist_factorform` (:584),
`ProductTriple.prodTwist_general_pair` (:592),
`ProductTriple.koDim_add` (:708),
`ProductTriple.oppgrandProd_flip` (:1131),
`ProductTriple.flipProd_involutive` (:505) /
`flipProd_CM_regular` (:516) / `prodFlip_CM_regular` (:526),
`TwistedTriple.flipTwist_involutive` (:714) / `flipTwist_mul`
(:720) / `flipTwist_add` (:727) / `flipTwist_one` (:734) /
`flipTwist_CM_regular` (:745),
`TwistedTriple.bimod_lr_compat` (:435, is `Matrix.mul_assoc`).
For the flip lemmas the equation proved *is* the claimed property
(flip CM-regularity = componentwise star-compatibility); the
triviality is the mathematical point, and both files say so.

## 6. Statement vs whitepaper-dossier comparison

Dossiers swept: `whitepaper/` grep for all eight module names
(36 files). Findings:

- **MISMATCH (by name): `cf_kernel_classification_46_10`,
  `cf_kernel_classification_full`, `ccm_classification` vs
  `whitepaper/grand-unified-theory.md`, Link 6 and the summary
  ledger.** The GUT paper (September 2026) presents them as
  "elimination logic proved… conditional on the stated T4 axiom"
  (grand-unified-theory.md:159–171, 197–211, 301–303) — i.e. the
  axiom as merely *unproved*. The Lean headers at the current
  tree state flag the consumed axiom **FALSE AS STATED /
  UNSOUND AS STATED** (2026-09-30 H4 retarget;
  CFKernelClassification.lean:122–131, CCMAlgebraClassification.lean:225–232),
  which is stronger than "conditional": a false axiom makes the
  conditional vacuous in the flagged domain. The GUT text does
  not carry the flag. Later dossiers DO:
  `whitepaper/gut-roadmap-2026-09-29.md` Step D ("computationally
  false as stated", :149–152) and
  `whitepaper/gap-theorem-queue-2026-10-24.md` (:527–537, flags
  `ccm_classification` and notes the corrected
  `CFKernel22.cf_kernel_classification_46_22`). So the mismatch
  is one stale dossier, not the ledger as a whole — reported by
  name at full rank per the pack.
- The GUT Link-6 English for `cf_kernel_classification_full`
  ("order-one + [D,C_F]=0 + self-adjointness + J-compatibility +
  grading-oddness forces D to be SM-type",
  grand-unified-theory.md:164–167) also inherits W2: the Lean
  proof uses only the first two hypotheses.
- Everything else checked matches its dossier English:
  rung-4 / rung-4-prep dossiers describe `pauliBounded` and
  `HasCompactResolvent` exactly as the files do (opaque window,
  content proved, rung-4-2026-10-11.md:12, 34–60);
  `corpus-dependency-audit-2026-10-21.md` §4/§6 agrees with the
  fresh footprints here (the two CF headlines + `ccm_classification`
  on the exotic axioms; `pauli_compactResolvent` depended on by
  no theorem, only the instance) — and this audit's fresh counts
  for the family are consistent with it. Product/Analytic/Bounded
  dossiers (rung-2/3/4-prep, foundations v1–v4) describe the
  class-data level and the scoped-out estimates as the files do;
  no dossier checked claims a constructed manifold factor, a
  proved compact resolvent, or a tensor-product norm estimate
  that the statements do not deliver.

## 7. Bottom line

- sorryAx: **0 / 208** — no empty (sorry) proofs in the family.
- Proved-only: **205 / 208**. Conditional: **3**, all in the
  CCM/CF classification pair, all on named T4 axioms.
- Weak: **2** — `ccm_classification` (W1),
  `cf_kernel_classification_full` (W2). Both are in the
  conditional pair; neither is in the six spectral-triple modules
  proper.
- The six modules' own headlines are, headline by headline,
  non-degenerate relative to their stated data: the finite triple
  (order-zero, γ-oddness, self-adjointness, conditional
  J-compatibility) is proved outright on concrete matrices; the
  twisted/Krein/causal material is proved outright on finite
  matrices, including its obstruction verdict; the
  product/analytic/bounded material is proved relative to
  honestly-labeled T2 class data, with existence/construction and
  the analytic estimates explicitly pinned where they are absent.
- Stale-dossier flag: `grand-unified-theory.md` Link 6 does not
  carry the 2026-09-30 UNSOUND-AS-STATED flag that the Lean
  headers and the later roadmap/gap-queue dossiers carry.

**NO CLAIM. Dials 0/4.**
