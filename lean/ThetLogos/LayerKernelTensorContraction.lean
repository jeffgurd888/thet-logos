/-
# WP2 character route, Module A — the finite-group contraction
# API in tensor-entry form (uniform in slot dimension)

Module A of the WP2 scope (`wp2-deltagramgap-scope-2026-11-16.md`
§3): the uniform finite-group contraction machinery for the
character route to `LayerKernelPos` at general finite `(G, ρ)`.
The scope's two cores (§2.2) are (1) the column expansion at
general `d` — Module B's B1 — and (2) the cyclic tensor-network
contraction at the site projections: the stratum average of a
product of column matrix coefficients reassembled as separated
squares.  This module builds core (2)'s API.

**Form of the API (a disclosed re-cut of the scope's working
labels, not of its content).**  The contraction is carried in
elementary tensor-entry form: for a finite slot type `κ` with
slot dimensions `n : κ → ℕ` and slot representations
`σ : ∀ j, G →* unitaryGroup (Fin (n j)) ℂ`, the tensor entry
`tensorEntry σ g A B = ∏ j, repMatrix (σ j) g (A j) (B j)` is
the matrix coefficient of the tensor representation.  Slot
dimensions vary because the assembly's slots carry different
column types (different irreducible constituents, of different
dimensions); `GramWordTensor`'s `tensorMat`/`occMat` are the
common-dimension case and are cited, not reproved, where they
apply.  The site average is the counting-measure average of a
tensor entry; A2 identifies it with T2's averaging operator
(`AveragingProjection.averagingOperator`, cited) on the slot
Euclidean space and decomposes it over an orthonormal basis of
the invariant subspace — the channel decomposition the
assembly consumes.  The scope's A3 (isotypic projectors for
tensor powers; the Clebsch–Gordan expansion of entry products)
is realized as: A1's entry calculus (the expansion of entry
products is `tensorEntry_mul`), A2's channel package applied
to arbitrary slot families — tensor powers included — and
A3's tensor-power character identities (`tensorTrace`).

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing in this
module routes through `StratumColumnFactorization` (dead for
every β > 0, K-TM-FACT / K-FACT-SEAT), and no feature built
from this API is constant at β > 0 by construction — the
features of the assembly are word data factors, and the F3
test `LayerKernelSOSCert.layerKernel_const_of_features_constant`
stays armed downstream.  This module proves no positivity and
closes nothing: `DeltaGramGap` is proved at no seat, no β, no
`d` (the instances proved to date on this line are
`LayerKernelPos` instances, by direct arguments or character
certificates — WP2 scope §5, correction 1); `LayerKernelPos`
at general finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of this
line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.GramWordTensor
import ThetLogos.LayerKernelGramCertFinite

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal

namespace ThetLogos

section TensorEntryAPI

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {n : κ → ℕ}
  (σ : ∀ j, G →* ↥(Matrix.unitaryGroup (Fin (n j)) ℂ))

/-- **The tensor entry** of a slot family at `g`: the product
over slots of the slot matrix coefficients,
`∏ j, repMatrix (σ j) g (A j) (B j)`.  This is the `(A, B)`
matrix coefficient of the tensor representation of `G` on
`∀ j, Fin (n j)`-indexed tensors; `GramWordTensor.tensorMat`
is the common-dimension special case. -/
def tensorEntry (g : G) (A B : ∀ j, Fin (n j)) : ℂ :=
  ∏ j, repMatrix (σ j) g (A j) (B j)

/-- The tensor entry at the identity is the Kronecker δ on
index tuples. -/
theorem tensorEntry_one (A B : ∀ j, Fin (n j)) :
    tensorEntry σ 1 A B = if A = B then 1 else 0 := by
  have hfac : ∀ j : κ, repMatrix (σ j) 1 (A j) (B j)
      = if A j = B j then (1 : ℂ) else 0 := by
    intro j
    rw [repMatrix_one]
    by_cases h : A j = B j <;> simp [h, Matrix.one_apply]
  rw [tensorEntry, Finset.prod_congr rfl (fun j _ => hfac j),
    prod_indicator_eq]
  by_cases h : A = B
  · rw [if_pos h, if_pos (fun j => congrFun h j)]
  · rw [if_neg h]
    refine if_neg (fun hall => h (funext hall))

/-- **The entry product law** (the Clebsch–Gordan expansion of
entry products, in the form the contraction consumes): the
tensor entry at a product is the path sum over intermediate
index tuples of the factor entries. -/
theorem tensorEntry_mul (g h : G) (A B : ∀ j, Fin (n j)) :
    tensorEntry σ (g * h) A B
      = ∑ C : ∀ j, Fin (n j),
        tensorEntry σ g A C * tensorEntry σ h C B := by
  have hfac : ∀ j : κ, repMatrix (σ j) (g * h) (A j) (B j)
      = ∑ c, repMatrix (σ j) g (A j) c
        * repMatrix (σ j) h c (B j) := by
    intro j
    rw [repMatrix_mul, Matrix.mul_apply]
  rw [tensorEntry, Finset.prod_congr rfl (fun j _ => hfac j),
    Fintype.prod_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [tensorEntry, tensorEntry, Finset.prod_mul_distrib]

/-- The conjugate of a tensor entry is the tensor entry of
the conjugate slot family (`conjRep` per slot). -/
theorem tensorEntry_star (g : G) (A B : ∀ j, Fin (n j)) :
    star (tensorEntry σ g A B)
      = tensorEntry (fun j => GramWordTensor.conjRep (σ j)) g A B := by
  rw [tensorEntry, tensorEntry, star_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [GramWordTensor.repMatrix_conjRep, GramWordTensor.conjMat_apply]

/-- The tensor entry at the inverse is the conjugate of the
transposed entry: unitarity, slot by slot. -/
theorem tensorEntry_inv (g : G) (A B : ∀ j, Fin (n j)) :
    tensorEntry σ g⁻¹ A B = star (tensorEntry σ g B A) := by
  rw [tensorEntry, tensorEntry, star_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [GramWordTensor.repMatrix_inv_entry, GramWordTensor.repMatrix_conjRep,
    GramWordTensor.conjMat_apply]

/-- **The tensor trace**: the diagonal sum of the tensor
entry — the character of the tensor representation. -/
def tensorTrace (g : G) : ℂ :=
  ∑ A : ∀ j, Fin (n j), tensorEntry σ g A A

/-- The tensor trace is the product of the slot characters:
traces multiply over slots (the character of a tensor power
is the power of the character — `GramWordTensor`'s
`tensorMat_trace` in varying-dimension form). -/
theorem tensorTrace_eq_prod (g : G) :
    tensorTrace σ g = ∏ j, charFn (σ j) g := by
  have hfac : ∀ j : κ, charFn (σ j) g
      = ∑ i : Fin (n j), repMatrix (σ j) g i i := fun j => rfl
  rw [tensorTrace, Finset.prod_congr rfl (fun j _ => hfac j),
    Fintype.prod_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rfl

/-- **The site average of a tensor entry** (counting measure):
the finite form of the `averageMap` site projection.  Its
channel decomposition is A2; here its intertwining property
— the average is a projection along the action — is proved. -/
noncomputable def tensorAvg (A B : ∀ j, Fin (n j)) : ℂ :=
  ((Fintype.card G : ℂ))⁻¹ * ∑ g, tensorEntry σ g A B

/-- **Intertwining (left half).**  Absorbing a slot action on
the left of the average returns the average: the average is
invariant under the tensor action, the projection property
of `averageMap` in entry form. -/
theorem tensorAvg_absorb_left (h : G) (A B : ∀ j, Fin (n j)) :
    ∑ C : ∀ j, Fin (n j),
        tensorEntry σ h A C * tensorAvg σ C B
      = tensorAvg σ A B := by
  calc ∑ C : ∀ j, Fin (n j),
          tensorEntry σ h A C * tensorAvg σ C B
      = ∑ C : ∀ j, Fin (n j), ((Fintype.card G : ℂ))⁻¹
          * ∑ g, tensorEntry σ h A C * tensorEntry σ g C B := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [tensorAvg, mul_left_comm, Finset.mul_sum]
    _ = ((Fintype.card G : ℂ))⁻¹
          * ∑ C : ∀ j, Fin (n j), ∑ g,
            tensorEntry σ h A C * tensorEntry σ g C B :=
        (Finset.mul_sum ..).symm
    _ = ((Fintype.card G : ℂ))⁻¹
          * ∑ g, ∑ C : ∀ j, Fin (n j),
            tensorEntry σ h A C * tensorEntry σ g C B := by
        rw [Finset.sum_comm]
    _ = ((Fintype.card G : ℂ))⁻¹
          * ∑ g, tensorEntry σ (h * g) A B := by
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        exact (tensorEntry_mul σ h g A B).symm
    _ = tensorAvg σ A B := by
        rw [tensorAvg]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft h)
          (fun g => tensorEntry σ g A B)

end TensorEntryAPI

end ThetLogos
