import ThetLogos.OrderOne
import ThetLogos.MartinettiRep
import ThetLogos.CFKernel

/-!
# ThetLogos.CFKernelClassification — 46 → 10 Dirac kernel reduction

Bridges the T4 numerical 46/10/36 census into a machine-checked Lean
classification. The 46-dimensional order-one nullspace `V₄₆`, under the
repaired `smGen` representation, is cut by `[D, C_F] = 0` to the
10-dimensional SM physical sector `V₁₀`.

## Algebraic mechanics

Let `V₄₆ ⊂ M₃₂(ℂ)` be the 46-dimensional real subspace of Hermitian matrices
satisfying `OrderOneHolds` under the repaired `smGen`/`smGenOp`.

* **Linear commutator operator:** `𝓛_{C_F}(D) = D * cfMat - cfMat * D`.
* **Restriction:** `𝓛_{C_F}|_{V₄₆} : V₄₆ → M₃₂(ℂ)` is linear.
* **Decoupling:** By `cfMat_comm_forces_block` (CFKernel.lean), any
  `D ∈ ker(𝓛_{C_F}|_{V₄₆})` vanishes on all couplings between the
  20-dimensional `C_F` support `{0,…,17,24,25}` and its 12-dimensional
  complement.
* **Kernel theorem:** The 10 SM parameters `{Y_ν, Y_e, Y_u, Y_d, Y_R} × {Re, Im}`
  span `V₁₀ ⊂ V₄₆` with `𝓛_{C_F} = 0` identically. The 36 exotic directions
  carry non-vanishing off-diagonal blocks across the support boundary, so
  `𝓛_{C_F}|_{V₄₆ ∖ V₁₀}` is injective. Hence `ker(𝓛_{C_F}|_{V₄₆}) = V₁₀`.

This is Q3.1 (C_F cuts the S-sector to the 8 SM Yukawas) and Q3.2 (C_F forces
the Majorana T-block to SM form) from the CCM proof.
-/

open Matrix

namespace ThetLogos

/-- Linear map taking a 32×32 Dirac operator to its commutator with C_F.
    This is the derivation `𝓛_{C_F}(D) = [D, cfMat]`. -/
def cfCommutatorMap (D : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  D * cfMat - cfMat * D

/-- The 10-dimensional Standard Model Yukawa/Majorana moduli space:
    exactly the image of the 5-complex-parameter `smDirac` ansatz. -/
def IsSMPhysicalSector (D : Matrix I32 I32 ℂ) : Prop :=
  ∃ (yNu yE yU yD yR : ℂ), D = smDirac yNu yE yU yD yR

/-- The 46-dimensional order-one nullspace, as a complex submodule of
    32×32 matrices. (The numerical census finds real dimension 46 on the
    Hermitian subspace; the complex span is used here for the module structure.) -/
def OrderOneNullspace : Submodule ℂ (Matrix I32 I32 ℂ) :=
  Submodule.span ℂ { D | OrderOneHolds D }

/-- The SM sector lies inside the order-one nullspace: the repaired
    `OrderOneHolds` is satisfied by every `smDirac` (via `smDirac_order_one`). -/
theorem smSector_mem_nullspace (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR ∈ OrderOneNullspace := by
  apply Submodule.subset_span
  exact OrderOneHolds_smDirac yNu yE yU yD yR

/-- `cfCommutatorMap` vanishes exactly when `[D, cfMat] = 0`. -/
theorem cfCommutatorMap_eq_zero_iff (D : Matrix I32 I32 ℂ) :
    cfCommutatorMap D = 0 ↔ D * cfMat - cfMat * D = 0 := Iff.rfl

/-- Classification target Q3.1/Q3.2 (46→10 form): order-one + `[D, C_F] = 0`
    forces `D` into the SM physical sector — the 10-dimensional moduli space.

    This is the streamlined version focusing on the commutator kernel. The
    fuller version with self-adjointness, J-compatibility, and grading-oddness
    is `cf_kernel_classification` in CFKernel.lean.

    Proof outline:
    * Step 1: `cfMat_comm_forces_block` enforces the 20/12 block-diagonal
      structure — `D` cannot connect the `C_F` support to its complement.
    * Step 2 (Q3.1): on the decoupled blocks, the order-one constraints under
      the repaired `smGen` collapse the 36 exotic directions; the S-sector
      reduces to the 8 SM Yukawa directions.
    * Step 3 (Q3.2): `[D, C_F] = 0` forces the Majorana T-block to the single
      SM direction `yR`.

    Status: the analytic core of Steps 2–3 (the 46→10 elimination) is OPEN.
    The T4 numerical census (attack4_corrected) confirms: 46-dim nullspace,
    10 SM directions satisfy `[D,C_F]=0` exactly, 36 extras fail (min norm
    0.318). -/
theorem cf_kernel_classification_46_10
    (D : Matrix I32 I32 ℂ)
    (h_order_one : OrderOneHolds D)
    (h_cf_comm : cfCommutatorMap D = 0) :
    IsSMPhysicalSector D := by
  -- Unfold the commutator map to the form `cfMat_comm_forces_block` expects.
  have h_comm : D * cfMat - cfMat * D = 0 := h_cf_comm
  -- Step 1: block-diagonal structure. For any i,j across the support boundary,
  -- D i j = 0.
  have h_block : ∀ (i j : I32), cfIndicator i ≠ cfIndicator j → D i j = 0 :=
    fun i j hij => cfMat_comm_forces_block D h_comm i j hij
  -- Step 2 (Q3.1, OPEN): order-one on the block-diagonal D kills the 36
  -- exotic directions, leaving the 8 Yukawa parameters.
  -- Step 3 (Q3.2, OPEN): the Majorana block is forced to SM form (yR).
  sorry

end ThetLogos
