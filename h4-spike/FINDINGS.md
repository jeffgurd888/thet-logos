# H4 Exact Pivot-Certificate Feasibility Spike — FINDINGS
Date: 2026-09-29

## Verdict: NO-GO (with a deeper soundness finding)

H4 cannot proceed as conceived. Beyond the expected "no exact basis data"
obstruction, the spike uncovered that the T4 `exotic_decomposition` axiom is
not merely unproved — it is FALSE as stated, and the theorem
`cf_kernel_classification_46_10` built on it is FALSE.

## Exact computation results (Python, mirror of Lean definitions)

All computations use an exact mirror of the Lean `smGen`/`smGenOp` definitions
(MartinettiRep.lean) and `OrderOneHolds` (OrderOne.lean, 144 pairs).

### 1. OrderOneHolds nullspace: 536 complex dims, NOT 46
- Built S = Σ_{144 pairs} L†L (L(D) = [[D,X],Y°]), exact eigvalsh.
- Eigenvalues: 536 exactly 0.0, then jump to exactly 1.0. Clean gap.
- **dim_ℂ(nullspace) = 536** (1072 real dims).
- The nullspace IS a coordinate subspace: exactly 536 matrix units E_ij
  satisfy all 144 pairs; since dim=536, nullspace = their span.
- Therefore OrderOneHolds(D) ⟺ D supported on 536 allowed positions
  (488 forbidden positions).

### 2. All 488 forbidden positions have singleton isolating equations
- For each forbidden (i,j), found (g1,g2,k,l,c≠0) with
  ([[D, smGen g1], smGenOp g2])_{kl} = c · D_{ij}.
- All 488/488 isolated. (Explicit coefficient formula derived and verified.)

### 3. Combined (OrderOneHolds + [D,C_F]=0): 440 complex dims, NOT 10
- cfMat = diagonal(cfIndicator) confirmed in CFKernelBase.lean.
- [D,cfMat]=0 ⟺ D_{ij}=0 when cf_i≠cf_j (support restriction).
- Combined nullspace = coordinate subspace on 440 positions.
- **dim_ℂ = 440.** The SM sector (image of smDirac: ℂ^5 → M_32) has dim ≤ 5.
- 440 > 5, therefore `cf_kernel_classification_46_10` is FALSE.

### 4. The axiom is false (dimension count)
- `exotic_decomposition` claims: order-one D ⟹ D = D_SM + Σ_{36} β_b E_b.
- RHS has dim_ℝ ≤ 10 + 36 = 46. LHS (OrderOneHolds) has dim_ℝ = 1072.
- 1072 > 46. The axiom is FALSE.
- Any theorem proved from it (`cf_kernel_classification_46_10`,
  `cf_kernel_classification_full`, `majorana_Eblock_rigidity`,
  `ccm_classification`) is UNSOUND (valid Lean proof, false axiom).

### 5. Root cause: 144-pair condition is too weak; 46-dim needs admissibility
- The 12 complex smGen do not linearly span π(A) (missing P_H, P_M).
- But even the 14-dim complex basis (196 pairs) gives the SAME 536-dim
  nullspace. So 12-vs-14 is not the issue.
- The 46-dim census used 576 real pairs WITHIN the 272-dim ADMISSIBLE
  subspace (self-adjoint + grading-odd + J-compatible).
- In the FULL space, even the full order-one condition gives 536-dim.
- The Lean `OrderOneHolds` lacks admissibility hypotheses, so the
  classification cannot hold as stated.

## Impact
- H4 (exact pivot certificate): NO-GO. There is no exact basis data, and
  the decomposition being "certified" does not hold.
- The 46→10 classification, its full J_F/γ_F version, and H13
  (majorana_Eblock_rigidity, just proved/pushed) all depend on the false
  axiom and are unsound as stated.
- This does NOT affect T3 results (TRO, three-gen inheritance, inner
  fluctuations) which do not use the axiom.

## Recommended repair direction
- Strengthen the classification hypotheses with admissibility
  (self-adjoint, grading-odd, J-compatible), matching the census domain.
- OR redefine `OrderOneHolds` to the 576-pair real version AND restrict
  to admissible D.
- Then re-verify the nullity is 46-dim (numerically first), and only then
  attempt an exact certificate (the 488 singleton equations give a
  mechanical proof path for the order-one part).

## Files
- This report: ~/workspace/thet-logos/h4-spike/FINDINGS.md
- Numerical data (attack4_corrected/results/): E36.npy, pivot_matrix.npy, etc.
- Note: the rounded pivot_matrix_int.npy IS exactly invertible (det ≠ 0,
  199 digits, verified Pi·adj = det·I in Python), but this certifies only
  the rounded surrogate, not the Lean predicate.
