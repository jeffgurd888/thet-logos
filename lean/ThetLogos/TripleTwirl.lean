import ThetLogos.LatticeTwirl
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-
# ThetLogos.TripleTwirl - TW-1: the (2,1) triple twirl as a projector
(SINGLE-LANE brick on the A >= 0 core chain)

**Governing memo:** `scoping-gram-dominance-2026-10-29.md` section 4.2
(TW-1 row) and section 2.2 (the seam this brick unblocks). Pack:
`pack-tw-1.md`.

## The registered deliverable, in the memo's words

Order 5's channel sites contract three factors at shared sites; their
evaluation is the (2,1) twirl, the group average of
rho x rho x rho-bar (and its (1,2) conjugate twin). The pair twirls
evaluated because Schur forces the invariant space of rho x rho-bar
(and rho x rho) to be one-dimensional - a line - and the trace pins
the projector's scalar. The invariant space of rho x rho x rho-bar
has dimension a(rho) = the multiplicity of rho in rho x rho (a
Clebsch-Gordan number of (G, rho)) - representation-dependent, NOT
forced to 1 (it is 1 for both probed seats' reps and for (S4, std);
it is 2 for the adjoint of SU(3)). TW-1's honest deliverable is
therefore a PROJECTOR FORMULA relative to a chosen invariant basis
(dimension a(rho), carried symbolically), not an entry formula.

## Verdict: FULL

The dimension a(rho) is carried symbolically throughout: every
general theorem below is quantified over an arbitrary finite group
G, an arbitrary unitary representation rho, and an arbitrary chosen
invariant basis indexed by `Fin a` with `a` a free variable of the
theorem. No general theorem specializes to a = 1. The a = 1 collapse
appears only in the labeled seat instance of the last section (the
trivial representation, where a(rho) = 1 is computed, not assumed).

## What is landed

1. The (2,1) triple twirl `triTwirl21` and the (1,2) conjugate twin
   `triTwirl12`, defined by FINITE averaging over the finite group G
   (the corpus's seats are finite groups: C3, S3, S4, Q8; at a
   finite seat the finite average is the Haar average against the
   normalized counting measure - this module proves the finite form
   directly and claims no Haar-general triple twirl).
2. The projector package, proved once for an abstract triple action
   and instantiated at both twins: the twirl is idempotent,
   self-adjoint (matrix star, the pair twirls' form), its range is
   exactly the invariant subspace, it fixes the invariant subspace
   pointwise, and it commutes with the triple action (both products
   with a group action matrix collapse to the twirl itself).
3. The projector formula relative to a chosen invariant basis:
   - orthonormal form: if (e_alpha) is a vecInner-orthonormal family
     spanning the invariant subspace, the twirl is
     `P v = sum_alpha vecInner (e_alpha) v . e_alpha`;
   - Gram form: for a general spanning family (e_alpha) whose Gram
     matrix `gramMat e` is invertible (invertibility is a stated
     hypothesis, in the instance-implicit form `[Invertible
     (gramMat e)]`), the twirl is
     `P v = sum_alpha ((gramMat e)^{-1} *v b)_alpha . e_alpha` with
     `b_beta = vecInner (e_beta) v`.
   Here `vecInner x y = sum_i star (x i) * y i` is the entry
   sesquilinear form on the tensor space, defined elementarily in
   this module (the plain Pi type carries no inner-product instance
   in this pin, so no typeclass inner product is used anywhere).
4. The dimension identity: for any vecInner-orthonormal spanning
   family indexed by `Fin a`, `trace (triTwirl21 rho) = a` and
   `finrank (invariant subspace) = a`, and the trace is the
   character average
   `(1/|G|) * sum_g chi(g) * chi(g) * star (chi(g))`,
   chi the character of rho. So the symbol a IS a(rho): the
   Clebsch-Gordan multiplicity, computed by the character formula,
   never specialized.
5. The seat instance, labeled as an instance: at the trivial
   representation (d = 1) the invariant subspace is everything,
   a(rho) = 1 by computation, the twirl is the identity, and the
   projector formula collapses to the scalar/line form
   `P v = vecInner e0 v . e0` for the single unit invariant vector
   e0 - the pair-twirl shape. Sanity check, NOT the general claim.
6. The GD-1 / GD-2 consumer interface, in the next section.

## The GD-1 / GD-2 consumer interface (stated on the face)

GD-2 (`ThetLogos.SepDoubledQuad`) landed PARTIAL at a named seam:
splitting either sub-sum of the doubled moment's subset expansion
(the opposite-copies sub-sum `doubledOppSum` and the same-side
sub-sum `doubledSameSum`) into row/column form requires evaluating
a TRIPLE SITE INTEGRAL - three incident entry factors at each of
the doubled column's two sites - which no module owned. This module
supplies exactly that evaluation, in entry form:

- `siteEval21`: at a shared site, the normalized finite average of
  two plain entry factors and one conjugated entry factor,
  `(1/|G|) sum_g rho(g) i1 j1 * rho(g) i2 j2 * star (rho(g) i3 j3)`,
  equals the (2,1) twirl entry
  `triTwirl21 rho ((i1, i2), i3) ((j1, j2), j3)`. This is the site
  integral carried by the doubled column's sites in BOTH of GD-2's
  sub-sums (the three incident factors there are two plain and one
  conjugated, up to the ordering of the copies).
- `siteEval12`: the conjugate twin `(1/|G|) sum_g rho(g) i1 j1 *
  star (rho(g) i2 j2) * star (rho(g) i3 j3)` equals the (1,2) twirl
  entry, for the mirrored (conjugated-copy) sites.
- The contracted form the assembly consumes is the projector
  formula itself (`triTwirl21_eq_gram_sum`,
  `triTwirl21_eq_sum_of_orthonormal`): a triple site contraction
  against any coefficient vector is the twirl applied to that
  vector, hence the Gram sum over the chosen invariant basis.

REMAINING STEP (named, GD-1's / GD-2-follow-on's work, NOT done
here): reassembling the site-wise projector evaluations into the
doubled network's row/column split - i.e. feeding `siteEval21` /
`siteEval12` through the R1 expansion of `doubledCharMoment` and
deciding whether the resulting network sum lies in the kappa4 cone
(GD-1) or separates (GD-2's fork). This module evaluates the site
integral; it does not perform the network reassembly, does not
prove GD-global at order 5, and does not touch Sep-weak.

**Fences.** NO CLAIM. Parts of the Clay Yang-Mills statement closed
by this module: 0. Dials: 0/4. Scope: finite groups G, finite-
dimensional unitary rho, irreducible or not (no irreducibility is
assumed anywhere - the projector package is representation-free).
NOT in the root import list (corpus pattern); verified by targeted
build.
-/

namespace ThetLogos

open Finset
open scoped Matrix

/-! ## The entry sesquilinear form on tensor spaces -/

section VecInner

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entry sesquilinear form on `ι → ℂ`:
`vecInner x y = ∑ i, star (x i) * y i`. Conjugate-linear in the
first argument, linear in the second. Defined elementarily: the
plain Pi type carries no inner-product typeclass instance in this
pin, and the Gram calculus below needs only these entry sums. -/
def vecInner (x y : ι → ℂ) : ℂ := ∑ i, star (x i) * y i

theorem vecInner_apply (x y : ι → ℂ) :
    vecInner x y = ∑ i, star (x i) * y i := rfl

theorem vecInner_zero_right (x : ι → ℂ) : vecInner x 0 = 0 := by
  simp [vecInner]

theorem vecInner_add_right (x y z : ι → ℂ) :
    vecInner x (y + z) = vecInner x y + vecInner x z := by
  rw [vecInner_apply, vecInner_apply, vecInner_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.add_apply, mul_add]

theorem vecInner_sub_right (x y z : ι → ℂ) :
    vecInner x (y - z) = vecInner x y - vecInner x z := by
  rw [vecInner_apply, vecInner_apply, vecInner_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.sub_apply, mul_sub]

theorem vecInner_smul_right (x y : ι → ℂ) (c : ℂ) :
    vecInner x (c • y) = c * vecInner x y := by
  rw [vecInner_apply, vecInner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    ring

theorem vecInner_sum_right {κ : Type*} (x : ι → ℂ) (s : Finset κ)
    (f : κ → (ι → ℂ)) :
    vecInner x (∑ k ∈ s, f k) = ∑ k ∈ s, vecInner x (f k) := by
  rw [vecInner_apply]
  have hterm : ∀ i : ι, star (x i) * (∑ k ∈ s, f k) i
      = ∑ k ∈ s, star (x i) * f k i := by
    intro i
    rw [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (vecInner_apply x (f k)).symm

theorem vecInner_single (x : ι → ℂ) (q : ι) (c : ℂ) :
    vecInner x (Pi.single q c) = star (x q) * c := by
  rw [vecInner_apply]
  rw [Finset.sum_eq_single q]
  · rw [Pi.single_eq_same]
  · intro p _ hpq
    rw [Pi.single_eq_of_ne hpq, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ q) h

end VecInner

/-! ## The abstract finite-averaging projector package

Everything in this section is proved for an abstract matrix action
`A : G → Matrix ι ι ℂ` of a finite group `G` satisfying the three
representation laws. The (2,1) and (1,2) triple actions are
instantiations; the pair twirls' Haar package in
`ThetLogos.LatticeTwirl` is the same shape at pair level. -/

section AbstractTwirl

variable {G : Type*} [Group G] [Fintype G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : G → Matrix ι ι ℂ)

theorem cardG_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by
  haveI : Nonempty G := ⟨1⟩
  exact Nat.cast_ne_zero.mpr Fintype.card_pos.ne'

/-- The finite-group average of the action `A`: the candidate
invariant projector `(1/|G|) • ∑ g, A g`. -/
noncomputable def avgTwirl : Matrix ι ι ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, A g

theorem avgTwirl_def :
    avgTwirl A = (Fintype.card G : ℂ)⁻¹ • ∑ g, A g := rfl

/-- The invariant submodule of the action `A`. -/
def avgInvariant : Submodule ℂ (ι → ℂ) where
  carrier := {w | ∀ h : G, A h *ᵥ w = w}
  add_mem' := by
    intro x y hx hy h
    rw [Matrix.mulVec_add, hx h, hy h]
  zero_mem' := by
    intro h
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c x hx h
    rw [Matrix.mulVec_smul, hx h]

theorem mem_avgInvariant (w : ι → ℂ) :
    w ∈ avgInvariant A ↔ ∀ h : G, A h *ᵥ w = w := Iff.rfl

theorem avgTwirl_apply (p q : ι) :
    avgTwirl A p q = (Fintype.card G : ℂ)⁻¹ * ∑ g, A g p q := by
  rw [avgTwirl_def, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

/-- Left absorption: a group action matrix absorbs the twirl. -/
theorem act_mul_avgTwirl
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) (h : G) :
    A h * avgTwirl A = avgTwirl A := by
  rw [avgTwirl_def, Matrix.mul_smul, Matrix.mul_sum]
  refine congrArg _ ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft h) A]
  exact Finset.sum_congr rfl fun g _ => (hAmul h g).symm

/-- Right absorption: the twirl absorbs a group action matrix. -/
theorem avgTwirl_mul_act
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) (h : G) :
    avgTwirl A * A h = avgTwirl A := by
  rw [avgTwirl_def, Matrix.smul_mul, Matrix.sum_mul]
  refine congrArg _ ?_
  rw [← Equiv.sum_comp (Equiv.mulRight h) A]
  exact Finset.sum_congr rfl fun g _ => (hAmul g h).symm

/-- The twirl commutes with the action: both orders of the product
collapse to the twirl itself. -/
theorem avgTwirl_commute_act
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) (h : G) :
    avgTwirl A * A h = A h * avgTwirl A := by
  rw [avgTwirl_mul_act A hAmul h, act_mul_avgTwirl A hAmul h]

/-- The twirl's range lies in the invariant submodule. -/
theorem avgTwirl_mulVec_mem
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) (w : ι → ℂ) :
    avgTwirl A *ᵥ w ∈ avgInvariant A := by
  intro h
  rw [Matrix.mulVec_mulVec, act_mul_avgTwirl A hAmul h]

/-- The twirl fixes every invariant vector. -/
theorem avgTwirl_mulVec_of_mem
    {w : ι → ℂ} (hw : w ∈ avgInvariant A) :
    avgTwirl A *ᵥ w = w := by
  rw [avgTwirl_def, Matrix.smul_mulVec, Matrix.sum_mulVec]
  have hfix : ∀ g : G, A g *ᵥ w = w := fun g => hw g
  rw [Finset.sum_congr rfl (fun g _ => hfix g), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (cardG_ne_zero (G := G)), one_smul]

/-- Idempotence: the twirl squared is the twirl. -/
theorem avgTwirl_mul_self
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) :
    avgTwirl A * avgTwirl A = avgTwirl A := by
  have h1 : ∀ g : G, avgTwirl A * A g = avgTwirl A :=
    fun g => avgTwirl_mul_act A hAmul g
  calc avgTwirl A * avgTwirl A
      = avgTwirl A * ((Fintype.card G : ℂ)⁻¹ • ∑ g, A g) := by
        rw [avgTwirl_def]
    _ = (Fintype.card G : ℂ)⁻¹ • (avgTwirl A * ∑ g, A g) := by
        rw [Matrix.mul_smul]
    _ = (Fintype.card G : ℂ)⁻¹ • ∑ g, avgTwirl A * A g := by
        rw [Matrix.mul_sum]
    _ = (Fintype.card G : ℂ)⁻¹ • ∑ _g : G, avgTwirl A := by
        rw [Finset.sum_congr rfl (fun g _ => h1 g)]
    _ = avgTwirl A := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
          smul_smul, inv_mul_cancel₀ (cardG_ne_zero (G := G)),
          one_smul]

/-- Self-adjointness in the pair twirls' form: the matrix star of
the twirl is the twirl. -/
theorem avgTwirl_star
    (hAinv : ∀ g : G, A g⁻¹ = star (A g)) :
    star (avgTwirl A) = avgTwirl A := by
  ext p q
  have hstar_card : star (Fintype.card G : ℂ) = (Fintype.card G : ℂ) := by simp
  have hterm : ∀ g : G, star (A g q p) = A g⁻¹ p q := by
    intro g
    rw [← Matrix.star_apply, ← hAinv g]
  have hsum : (∑ g, star (A g q p)) = ∑ g, A g p q := by
    rw [Finset.sum_congr rfl (fun g _ => hterm g)]
    simpa only [Equiv.inv_apply] using
      Equiv.sum_comp (Equiv.inv G) (fun g => A g p q)
  rw [Matrix.star_apply, avgTwirl_apply, avgTwirl_apply, star_mul,
    star_inv₀, hstar_card, star_sum, hsum]
  exact mul_comm _ _

/-- The projector package: the twirl, as a linear map, is the
projection onto the invariant submodule. -/
theorem avgTwirl_isProj
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) :
    LinearMap.IsProj (avgInvariant A) (Matrix.mulVecLin (avgTwirl A)) where
  map_mem := fun w => by
    rw [Matrix.mulVecLin_apply]
    exact avgTwirl_mulVec_mem A hAmul w
  map_id := fun w hw => by
    rw [Matrix.mulVecLin_apply]
    exact avgTwirl_mulVec_of_mem A hw

/-- The twirl's range is exactly the invariant submodule. -/
theorem avgTwirl_range
    (hAmul : ∀ g h : G, A (g * h) = A g * A h) :
    LinearMap.range (Matrix.mulVecLin (avgTwirl A)) = avgInvariant A := by
  apply le_antisymm
  · rintro w ⟨x, hx⟩
    rw [← hx, Matrix.mulVecLin_apply]
    exact avgTwirl_mulVec_mem A hAmul x
  · intro w hw
    refine ⟨w, ?_⟩
    rw [Matrix.mulVecLin_apply]
    exact avgTwirl_mulVec_of_mem A hw

/-- The trace of the twirl is the averaged character of the
action. -/
theorem avgTwirl_trace :
    Matrix.trace (avgTwirl A)
      = (Fintype.card G : ℂ)⁻¹ * ∑ g, Matrix.trace (A g) := by
  show (∑ p : ι, avgTwirl A p p) = _
  have h1 : ∀ p : ι, avgTwirl A p p
      = (Fintype.card G : ℂ)⁻¹ * ∑ g, A g p p :=
    fun p => avgTwirl_apply A p p
  rw [Finset.sum_congr rfl (fun p _ => h1 p), ← Finset.mul_sum,
    Finset.sum_comm]
  refine congrArg _ ?_
  exact Finset.sum_congr rfl fun g _ => rfl

/-- Adjoint identity for `vecInner`: the twirl is self-adjoint
against the entry sesquilinear form. -/
theorem vecInner_avgTwirl
    (hAinv : ∀ g : G, A g⁻¹ = star (A g)) (x y : ι → ℂ) :
    vecInner x (avgTwirl A *ᵥ y) = vecInner (avgTwirl A *ᵥ x) y := by
  have hstarP : star (avgTwirl A) = avgTwirl A := avgTwirl_star A hAinv
  have hentry : ∀ p q : ι, star (avgTwirl A q p) = avgTwirl A p q := by
    intro p q
    have h := congrFun (congrFun hstarP p) q
    rwa [Matrix.star_apply] at h
  calc vecInner x (avgTwirl A *ᵥ y)
      = ∑ p, ∑ q, star (x p) * (avgTwirl A p q * y q) := by
        rw [vecInner_apply]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mat_mulVec_apply, Finset.mul_sum]
    _ = ∑ q, ∑ p, star (x p) * (avgTwirl A p q * y q) := Finset.sum_comm
    _ = ∑ q, ∑ p, (avgTwirl A p q * star (x p)) * y q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = vecInner (avgTwirl A *ᵥ x) y := by
        rw [vecInner_apply]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_mul]
        refine congrArg (· * y q) ?_
        rw [mat_mulVec_apply, star_sum]
        exact Finset.sum_congr rfl fun p _ => by
          rw [star_mul, hentry p q]
          exact mul_comm _ _

end AbstractTwirl

/-! ## The projector formula relative to a chosen invariant basis

Abstract form: `A` is an action as before, `e : Fin a → (ι → ℂ)` a
family of invariant vectors. The symbol `a` is a free variable of
every theorem in this section. -/

section AbstractGram

variable {G : Type*} [Group G] [Fintype G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : G → Matrix ι ι ℂ)
variable {a : ℕ} (e : Fin a → (ι → ℂ))

/-- The Gram matrix of the family `e` against `vecInner`:
`gramMat e i j = vecInner (e i) (e j)`. -/
def gramMat : Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun i j => vecInner (e i) (e j)

theorem gramMat_apply (i j : Fin a) :
    gramMat e i j = vecInner (e i) (e j) := rfl

/-- Coefficients are read off by the Gram matrix: pairing a
combination of the `e i` against `e β` applies the Gram matrix to
the coefficient vector. -/
theorem vecInner_combination (c : Fin a → ℂ) (β : Fin a) :
    vecInner (e β) (∑ i, c i • e i) = (gramMat e *ᵥ c) β := by
  rw [vecInner_sum_right, mat_mulVec_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vecInner_smul_right, gramMat_apply]
  exact mul_comm _ _

/-- The expansion of an invariant vector in a vecInner-orthonormal
spanning family: the coefficients are the pairings against the
family itself. -/
theorem expansion_of_orthonormal
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : avgInvariant A ≤ Submodule.span ℂ (Set.range e))
    {w : ι → ℂ} (hw : w ∈ avgInvariant A) :
    w = ∑ i, vecInner (e i) w • e i := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).1 (hspan hw)
  have hcoeff : ∀ β : Fin a, vecInner (e β) w = c β := by
    intro β
    rw [← hc, vecInner_combination]
    rw [mat_mulVec_apply]
    rw [Finset.sum_eq_single β]
    · rw [gramMat_apply, heorth β β, if_pos rfl, one_mul]
    · intro i _ hi
      rw [gramMat_apply, heorth β i, if_neg (Ne.symm hi), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ β) h
  calc w = ∑ i, c i • e i := hc.symm
    _ = ∑ i, vecInner (e i) w • e i :=
        Finset.sum_congr rfl fun i _ => by rw [hcoeff i]

/-- **The orthonormal projector formula (abstract form).** If the
invariant family `e` is vecInner-orthonormal and spans the
invariant subspace, the twirl is the Gram sum over `e`. -/
theorem avgTwirl_eq_sum_of_orthonormal
    (hAmul : ∀ g h : G, A (g * h) = A g * A h)
    (hAinv : ∀ g : G, A g⁻¹ = star (A g))
    (he_mem : ∀ i, e i ∈ avgInvariant A)
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : avgInvariant A ≤ Submodule.span ℂ (Set.range e))
    (v : ι → ℂ) :
    avgTwirl A *ᵥ v = ∑ i, vecInner (e i) v • e i := by
  have hmem : avgTwirl A *ᵥ v ∈ avgInvariant A :=
    avgTwirl_mulVec_mem A hAmul v
  rw [expansion_of_orthonormal A e heorth hspan hmem]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : vecInner (e i) (avgTwirl A *ᵥ v)
      = vecInner (avgTwirl A *ᵥ e i) v :=
    vecInner_avgTwirl A hAinv (e i) v
  rw [h1, avgTwirl_mulVec_of_mem A (he_mem i)]

/-- **The Gram projector formula (abstract form).** For a spanning
invariant family `e` whose Gram matrix is invertible, the twirl is
the Gram sum: coefficients are the inverse Gram matrix applied to
the pairing vector. The invertibility of the Gram matrix is a
stated hypothesis (instance form), exactly as the pack permits. -/
theorem avgTwirl_eq_gram_sum
    (hAmul : ∀ g h : G, A (g * h) = A g * A h)
    (hAinv : ∀ g : G, A g⁻¹ = star (A g))
    (he_mem : ∀ i, e i ∈ avgInvariant A)
    (hspan : avgInvariant A ≤ Submodule.span ℂ (Set.range e))
    [Invertible (gramMat e)]
    (v : ι → ℂ) :
    avgTwirl A *ᵥ v
      = ∑ α, ((gramMat e)⁻¹ *ᵥ (fun β => vecInner (e β) v)) α • e α := by
  set bvec : Fin a → ℂ := fun β => vecInner (e β) v with hbvec
  set c : Fin a → ℂ := (gramMat e)⁻¹ *ᵥ bvec with hc
  set w : ι → ℂ := ∑ α, c α • e α with hw_def
  have hw_mem : w ∈ avgInvariant A := by
    rw [hw_def]
    exact Submodule.sum_mem _ fun α _ =>
      Submodule.smul_mem _ _ (he_mem α)
  have hpair_w : ∀ β : Fin a, vecInner (e β) w = bvec β := by
    intro β
    have h1 : vecInner (e β) w = (gramMat e *ᵥ c) β :=
      vecInner_combination e c β
    rw [h1, hc, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hpair_P : ∀ β : Fin a, vecInner (e β) (avgTwirl A *ᵥ v) = bvec β := by
    intro β
    have h1 : vecInner (e β) (avgTwirl A *ᵥ v)
        = vecInner (avgTwirl A *ᵥ e β) v :=
      vecInner_avgTwirl A hAinv (e β) v
    rw [h1, avgTwirl_mulVec_of_mem A (he_mem β)]
  have hmem : avgTwirl A *ᵥ v ∈ avgInvariant A :=
    avgTwirl_mulVec_mem A hAmul v
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).1
    (hspan (Submodule.sub_mem _ hmem hw_mem))
  have hGram_d : gramMat e *ᵥ d = 0 := by
    funext β
    have h1 : (gramMat e *ᵥ d) β
        = vecInner (e β) (avgTwirl A *ᵥ v - w) := by
      rw [← vecInner_combination e d β, ← hd]
    rw [h1, vecInner_sub_right, hpair_P β, hpair_w β, sub_self,
      Pi.zero_apply]
  have hd0 : d = 0 := by
    have h2 := congrArg (fun u => (gramMat e)⁻¹ *ᵥ u) hGram_d
    simp only [Matrix.mulVec_zero] at h2
    rwa [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] at h2
  have hx0 : avgTwirl A *ᵥ v - w = 0 := by
    rw [← hd, hd0]
    simp
  exact sub_eq_zero.1 hx0

/-- The Gram matrix of a vecInner-orthonormal family is the
identity, so the Gram formula collapses to the orthonormal
formula for such a family. -/
theorem gramMat_eq_one_of_orthonormal
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0) :
    gramMat e = 1 := by
  ext i j
  rw [gramMat_apply, heorth i j, Matrix.one_apply]

/-- A vecInner-orthonormal family is linearly independent: its
coefficients are read off by pairing, and pairing against the
zero combination gives zero. -/
theorem linearIndependent_of_orthonormal
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0) :
    LinearIndependent ℂ e := by
  rw [linearIndependent_iff']
  intro s g hg β hβ
  have h1 : vecInner (e β) (∑ i ∈ s, g i • e i) = g β := by
    rw [vecInner_sum_right]
    rw [Finset.sum_eq_single β]
    · rw [vecInner_smul_right, heorth β β, if_pos rfl, mul_one]
    · intro i _ hi
      rw [vecInner_smul_right, heorth β i, if_neg (Ne.symm hi),
        mul_zero]
    · intro h
      exact absurd hβ h
  rw [hg, vecInner_zero_right] at h1
  exact h1.symm

/-- The invariant dimension seen by an orthonormal spanning
family: the finrank of the invariant submodule is the family's
index count `a`. -/
theorem avgInvariant_finrank_eq_of_orthonormal
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : avgInvariant A = Submodule.span ℂ (Set.range e)) :
    Module.finrank ℂ (avgInvariant A) = a := by
  rw [hspan]
  have h := finrank_span_eq_card (linearIndependent_of_orthonormal e heorth)
  rwa [Fintype.card_fin] at h

/-- The trace of the twirl seen by an orthonormal spanning family:
the trace is the family's index count `a` (as a complex number). -/
theorem avgTwirl_trace_eq_of_orthonormal
    (hAmul : ∀ g h : G, A (g * h) = A g * A h)
    (hAinv : ∀ g : G, A g⁻¹ = star (A g))
    (he_mem : ∀ i, e i ∈ avgInvariant A)
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : avgInvariant A ≤ Submodule.span ℂ (Set.range e)) :
    Matrix.trace (avgTwirl A) = (a : ℂ) := by
  have hentry : ∀ p q : ι, avgTwirl A p q
      = ∑ α, star (e α q) * e α p := by
    intro p q
    have h1 : avgTwirl A *ᵥ Pi.single q 1
        = ∑ α, vecInner (e α) (Pi.single q 1) • e α :=
      avgTwirl_eq_sum_of_orthonormal A e hAmul hAinv he_mem heorth
        hspan (Pi.single q 1)
    have h2 : (avgTwirl A *ᵥ Pi.single q 1) p = avgTwirl A p q := by
      rw [mat_mulVec_apply]
      rw [Finset.sum_eq_single q]
      · rw [Pi.single_eq_same, mul_one]
      · intro r _ hrq
        rw [Pi.single_eq_of_ne hrq, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ q) h
    rw [← h2, h1]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Pi.smul_apply, vecInner_single, smul_eq_mul, mul_one]
  show (∑ p : ι, avgTwirl A p p) = _
  rw [Finset.sum_congr rfl (fun p _ => hentry p p), Finset.sum_comm]
  have hnorm : ∀ α : Fin a, ∑ p : ι, star (e α p) * e α p = 1 := by
    intro α
    have h := heorth α α
    rw [if_pos rfl] at h
    exact h
  rw [Finset.sum_congr rfl (fun α _ => hnorm α)]
  simp

end AbstractGram

/-! ## The triple action matrices

The triple Kronecker matrix `triMat A B C` is the entry-form
Kronecker product on the index type `(Fin d × Fin d) × Fin d`
(the corpus's `pairMat` is stated for `Fin`-indexed factors only,
so the triple product is defined directly here; its
multiplicativity proof is the pair proof's sum factorization,
nested). The conjugate factor is the corpus's `orientConj`
(entrywise star), the same conjugate representation the pair
twirls use. The corpus's `orientConj` multiplicativity lemmas
carry a topological-group context the finite average does not
need, so the three factor laws are re-proved entrywise here as
`conjRep_mul`, `conjRep_one`, `conjRep_inv`. -/

section TripleAction

variable {G : Type*} [Group G] [Fintype G] {d : ℕ}
variable (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The triple Kronecker action matrix on
`(Fin d × Fin d) × Fin d`, in entry form. -/
def triMat (A B C : Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  Matrix.of fun p q => A p.1.1 q.1.1 * B p.1.2 q.1.2 * C p.2 q.2

theorem triMat_apply (A B C : Matrix (Fin d) (Fin d) ℂ)
    (p q : (Fin d × Fin d) × Fin d) :
    triMat A B C p q
      = A p.1.1 q.1.1 * B p.1.2 q.1.2 * C p.2 q.2 := rfl

theorem triMat_mul (A B C A' B' C' : Matrix (Fin d) (Fin d) ℂ) :
    triMat A B C * triMat A' B' C'
      = triMat (A * A') (B * B') (C * C') := by
  ext p r
  rw [Matrix.mul_apply]
  have hterm : ∀ q : (Fin d × Fin d) × Fin d,
      triMat A B C p q * triMat A' B' C' q r
        = (A p.1.1 q.1.1 * A' q.1.1 r.1.1)
          * (B p.1.2 q.1.2 * B' q.1.2 r.1.2)
          * (C p.2 q.2 * C' q.2 r.2) := by
    intro q
    rw [triMat_apply, triMat_apply]
    ring
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Fintype.sum_prod_type]
  have hinner : ∀ x : Fin d × Fin d,
      (∑ k : Fin d, (A p.1.1 x.1 * A' x.1 r.1.1)
          * (B p.1.2 x.2 * B' x.2 r.1.2) * (C p.2 k * C' k r.2))
        = ((A p.1.1 x.1 * A' x.1 r.1.1)
            * (B p.1.2 x.2 * B' x.2 r.1.2))
          * ∑ k : Fin d, C p.2 k * C' k r.2 := by
    intro x
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_mul]
  have hpair : (∑ x : Fin d × Fin d,
        (A p.1.1 x.1 * A' x.1 r.1.1) * (B p.1.2 x.2 * B' x.2 r.1.2))
      = (∑ i, A p.1.1 i * A' i r.1.1)
        * ∑ j, B p.1.2 j * B' j r.1.2 :=
    sum_prod_mul (fun i => A p.1.1 i * A' i r.1.1)
      (fun j => B p.1.2 j * B' j r.1.2)
  rw [hpair, triMat_apply, Matrix.mul_apply, Matrix.mul_apply,
    Matrix.mul_apply]

theorem triMat_one :
    triMat (1 : Matrix (Fin d) (Fin d) ℂ) 1 1 = 1 := by
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    by_cases hc : c = c' <;>
    simp [triMat_apply, Matrix.one_apply, ha, hb, hc, Prod.ext_iff]

theorem triMat_star (A B C : Matrix (Fin d) (Fin d) ℂ) :
    star (triMat A B C) = triMat (star A) (star B) (star C) := by
  ext p q
  rw [Matrix.star_apply, triMat_apply, triMat_apply, Matrix.star_apply,
    Matrix.star_apply, Matrix.star_apply, star_mul, star_mul]
  ring

/-- Entry form of the conjugate factor, from the definition
(the corpus's `conjEntry` carries its section's
topological-group instances as arguments; this copy is proved
from the definition and is instance-free). -/
theorem conjEntry (M : G → Matrix (Fin d) (Fin d) ℂ) (g : G)
    (a c : Fin d) :
    orientConj M g a c = star (M g a c) := rfl

/-- Multiplicativity of the conjugate factor, entrywise form
(the corpus's `orientConj_mul`, re-proved without the topological
context its section carries). -/
theorem conjRep_mul (M : G → Matrix (Fin d) (Fin d) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (g h : G) :
    orientConj M (g * h) = orientConj M g * orientConj M h := by
  ext a c
  rw [conjEntry, hmul, Matrix.mul_apply, Matrix.mul_apply,
    star_sum]
  exact Finset.sum_congr rfl fun k _ => by
    simp only [conjEntry, star_mul]
    exact mul_comm _ _

/-- Unit law of the conjugate factor, entrywise form. -/
theorem conjRep_one (M : G → Matrix (Fin d) (Fin d) ℂ)
    (hone : M 1 = 1) :
    orientConj M 1 = 1 := by
  ext a c
  rw [conjEntry, hone]
  by_cases h : a = c <;> simp [Matrix.one_apply, h]

/-- Inverse law of the conjugate factor, entrywise form. -/
theorem conjRep_inv (M : G → Matrix (Fin d) (Fin d) ℂ)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    orientConj M g⁻¹ = star (orientConj M g) := by
  ext a c
  rw [conjEntry, Matrix.star_apply, conjEntry, hinv,
    Matrix.star_apply]

/-- The (2,1) triple action: rho, rho, rho-bar. -/
def triAct21 (g : G) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  triMat (repMatrix ρ g) (repMatrix ρ g) (orientConj (repMatrix ρ) g)

/-- The (1,2) triple action, the conjugate twin: rho, rho-bar,
rho-bar. -/
def triAct12 (g : G) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  triMat (repMatrix ρ g) (orientConj (repMatrix ρ) g)
    (orientConj (repMatrix ρ) g)

theorem triAct21_mul (g h : G) :
    triAct21 ρ (g * h) = triAct21 ρ g * triAct21 ρ h := by
  unfold triAct21
  rw [triMat_mul, repMatrix_mul,
    conjRep_mul _ (fun a b => repMatrix_mul ρ a b)]

theorem triAct21_one : triAct21 ρ 1 = 1 := by
  unfold triAct21
  rw [repMatrix_one, conjRep_one _ (repMatrix_one ρ), triMat_one]

theorem triAct21_inv (g : G) :
    triAct21 ρ g⁻¹ = star (triAct21 ρ g) := by
  unfold triAct21
  rw [triMat_star, repMatrix_inv,
    conjRep_inv _ (fun a => repMatrix_inv ρ a)]

theorem triAct12_mul (g h : G) :
    triAct12 ρ (g * h) = triAct12 ρ g * triAct12 ρ h := by
  unfold triAct12
  rw [triMat_mul, repMatrix_mul,
    conjRep_mul _ (fun a b => repMatrix_mul ρ a b)]

theorem triAct12_one : triAct12 ρ 1 = 1 := by
  unfold triAct12
  rw [repMatrix_one, conjRep_one _ (repMatrix_one ρ), triMat_one]

theorem triAct12_inv (g : G) :
    triAct12 ρ g⁻¹ = star (triAct12 ρ g) := by
  unfold triAct12
  rw [triMat_star, repMatrix_inv,
    conjRep_inv _ (fun a => repMatrix_inv ρ a)]

/-- The (2,1) triple twirl: the finite average of the (2,1)
action. -/
noncomputable def triTwirl21 :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  avgTwirl (triAct21 ρ)

/-- The (1,2) triple twirl, the conjugate twin. -/
noncomputable def triTwirl12 :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  avgTwirl (triAct12 ρ)

/-- The invariant subspace of the (2,1) action: the space whose
dimension is a(rho). -/
def triInvariant21 : Submodule ℂ (((Fin d × Fin d) × Fin d) → ℂ) :=
  avgInvariant (triAct21 ρ)

/-- The invariant subspace of the (1,2) action. -/
def triInvariant12 : Submodule ℂ (((Fin d × Fin d) × Fin d) → ℂ) :=
  avgInvariant (triAct12 ρ)

/-- a(rho) for the (2,1) action: the dimension of the invariant
subspace of rho x rho x rho-bar, i.e. the multiplicity of rho in
rho x rho. A definition, carried symbolically in every theorem
that mentions it. -/
noncomputable def triDim21 : ℕ := Module.finrank ℂ (triInvariant21 ρ)

theorem triTwirl21_apply (p q : (Fin d × Fin d) × Fin d) :
    triTwirl21 ρ p q
      = (Fintype.card G : ℂ)⁻¹ * ∑ g,
        repMatrix ρ g p.1.1 q.1.1 * repMatrix ρ g p.1.2 q.1.2
          * star (repMatrix ρ g p.2 q.2) := by
  unfold triTwirl21
  rw [avgTwirl_apply]
  refine congrArg _ ?_
  exact Finset.sum_congr rfl fun g _ => triMat_apply _ _ _ _ _

theorem triTwirl12_apply (p q : (Fin d × Fin d) × Fin d) :
    triTwirl12 ρ p q
      = (Fintype.card G : ℂ)⁻¹ * ∑ g,
        repMatrix ρ g p.1.1 q.1.1 * star (repMatrix ρ g p.1.2 q.1.2)
          * star (repMatrix ρ g p.2 q.2) := by
  unfold triTwirl12
  rw [avgTwirl_apply]
  refine congrArg _ ?_
  exact Finset.sum_congr rfl fun g _ => triMat_apply _ _ _ _ _

/-- **Site evaluation, (2,1) form** (the GD-2 interface): the
normalized finite average of two plain entry factors and one
conjugated entry factor at a shared site is the (2,1) twirl
entry. -/
theorem siteEval21 (i1 i2 i3 j1 j2 j3 : Fin d) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g,
        repMatrix ρ g i1 j1 * repMatrix ρ g i2 j2
          * star (repMatrix ρ g i3 j3)
      = triTwirl21 ρ ((i1, i2), i3) ((j1, j2), j3) :=
  (triTwirl21_apply ρ ((i1, i2), i3) ((j1, j2), j3)).symm

/-- **Site evaluation, (1,2) form** (the conjugate twin): the
normalized finite average of one plain entry factor and two
conjugated entry factors at a shared site is the (1,2) twirl
entry. -/
theorem siteEval12 (i1 i2 i3 j1 j2 j3 : Fin d) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g,
        repMatrix ρ g i1 j1 * star (repMatrix ρ g i2 j2)
          * star (repMatrix ρ g i3 j3)
      = triTwirl12 ρ ((i1, i2), i3) ((j1, j2), j3) :=
  (triTwirl12_apply ρ ((i1, i2), i3) ((j1, j2), j3)).symm

/-! ### The (2,1) projector package -/

theorem triTwirl21_mulVec_mem (w : ((Fin d × Fin d) × Fin d) → ℂ) :
    triTwirl21 ρ *ᵥ w ∈ triInvariant21 ρ :=
  avgTwirl_mulVec_mem _ (fun g h => triAct21_mul ρ g h) w

theorem triTwirl21_mulVec_of_mem {w : ((Fin d × Fin d) × Fin d) → ℂ}
    (hw : w ∈ triInvariant21 ρ) :
    triTwirl21 ρ *ᵥ w = w :=
  avgTwirl_mulVec_of_mem _ hw

theorem triTwirl21_mul_self :
    triTwirl21 ρ * triTwirl21 ρ = triTwirl21 ρ :=
  avgTwirl_mul_self _ (fun g h => triAct21_mul ρ g h)

theorem triTwirl21_star : star (triTwirl21 ρ) = triTwirl21 ρ :=
  avgTwirl_star _ (fun g => triAct21_inv ρ g)

theorem triTwirl21_commute (h : G) :
    triTwirl21 ρ * triAct21 ρ h = triAct21 ρ h * triTwirl21 ρ :=
  avgTwirl_commute_act _ (fun g h => triAct21_mul ρ g h) h

theorem triTwirl21_isProj :
    LinearMap.IsProj (triInvariant21 ρ)
      (Matrix.mulVecLin (triTwirl21 ρ)) :=
  avgTwirl_isProj _ (fun g h => triAct21_mul ρ g h)

theorem triTwirl21_range :
    LinearMap.range (Matrix.mulVecLin (triTwirl21 ρ))
      = triInvariant21 ρ :=
  avgTwirl_range _ (fun g h => triAct21_mul ρ g h)

/-- **The (2,1) projector formula, orthonormal form.** Relative
to a chosen vecInner-orthonormal basis `e` of the (2,1)
invariant subspace, indexed by `Fin a` with `a` symbolic, the
(2,1) twirl is the Gram sum over `e`. -/
theorem triTwirl21_eq_sum_of_orthonormal {a : ℕ}
    (e : Fin a → (((Fin d × Fin d) × Fin d) → ℂ))
    (he_mem : ∀ i, e i ∈ triInvariant21 ρ)
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : triInvariant21 ρ
      ≤ Submodule.span ℂ (Set.range e))
    (v : ((Fin d × Fin d) × Fin d) → ℂ) :
    triTwirl21 ρ *ᵥ v = ∑ i, vecInner (e i) v • e i :=
  avgTwirl_eq_sum_of_orthonormal _ e (fun g h => triAct21_mul ρ g h)
    (fun g => triAct21_inv ρ g) he_mem heorth hspan v

/-- **The (2,1) projector formula, Gram form.** Relative to a
chosen spanning invariant family `e` indexed by `Fin a` with `a`
symbolic, with the Gram matrix of `e` invertible (stated
hypothesis), the (2,1) twirl is the inverse-Gram sum over `e`. -/
theorem triTwirl21_eq_gram_sum {a : ℕ}
    (e : Fin a → (((Fin d × Fin d) × Fin d) → ℂ))
    (he_mem : ∀ i, e i ∈ triInvariant21 ρ)
    (hspan : triInvariant21 ρ
      ≤ Submodule.span ℂ (Set.range e))
    [Invertible (gramMat e)]
    (v : ((Fin d × Fin d) × Fin d) → ℂ) :
    triTwirl21 ρ *ᵥ v
      = ∑ α, ((gramMat e)⁻¹ *ᵥ (fun β => vecInner (e β) v)) α
          • e α :=
  avgTwirl_eq_gram_sum _ e (fun g h => triAct21_mul ρ g h)
    (fun g => triAct21_inv ρ g) he_mem hspan v

/-- The dimension identity at (2,1): for a chosen orthonormal
basis of the invariant subspace indexed by `Fin a`,
a(rho) = `a` - the symbol is the dimension, for every basis. -/
theorem triDim21_eq_of_orthonormal {a : ℕ}
    (e : Fin a → (((Fin d × Fin d) × Fin d) → ℂ))
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : triInvariant21 ρ
      = Submodule.span ℂ (Set.range e)) :
    triDim21 ρ = a :=
  avgInvariant_finrank_eq_of_orthonormal _ e heorth hspan

/-! ### The (1,2) projector package (conjugate twin) -/

theorem triTwirl12_mulVec_mem (w : ((Fin d × Fin d) × Fin d) → ℂ) :
    triTwirl12 ρ *ᵥ w ∈ triInvariant12 ρ :=
  avgTwirl_mulVec_mem _ (fun g h => triAct12_mul ρ g h) w

theorem triTwirl12_mulVec_of_mem {w : ((Fin d × Fin d) × Fin d) → ℂ}
    (hw : w ∈ triInvariant12 ρ) :
    triTwirl12 ρ *ᵥ w = w :=
  avgTwirl_mulVec_of_mem _ hw

theorem triTwirl12_mul_self :
    triTwirl12 ρ * triTwirl12 ρ = triTwirl12 ρ :=
  avgTwirl_mul_self _ (fun g h => triAct12_mul ρ g h)

theorem triTwirl12_star : star (triTwirl12 ρ) = triTwirl12 ρ :=
  avgTwirl_star _ (fun g => triAct12_inv ρ g)

theorem triTwirl12_commute (h : G) :
    triTwirl12 ρ * triAct12 ρ h = triAct12 ρ h * triTwirl12 ρ :=
  avgTwirl_commute_act _ (fun g h => triAct12_mul ρ g h) h

theorem triTwirl12_isProj :
    LinearMap.IsProj (triInvariant12 ρ)
      (Matrix.mulVecLin (triTwirl12 ρ)) :=
  avgTwirl_isProj _ (fun g h => triAct12_mul ρ g h)

theorem triTwirl12_range :
    LinearMap.range (Matrix.mulVecLin (triTwirl12 ρ))
      = triInvariant12 ρ :=
  avgTwirl_range _ (fun g h => triAct12_mul ρ g h)

/-- **The (1,2) projector formula, orthonormal form** (conjugate
twin of the (2,1) formula). -/
theorem triTwirl12_eq_sum_of_orthonormal {a : ℕ}
    (e : Fin a → (((Fin d × Fin d) × Fin d) → ℂ))
    (he_mem : ∀ i, e i ∈ triInvariant12 ρ)
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : triInvariant12 ρ
      ≤ Submodule.span ℂ (Set.range e))
    (v : ((Fin d × Fin d) × Fin d) → ℂ) :
    triTwirl12 ρ *ᵥ v = ∑ i, vecInner (e i) v • e i :=
  avgTwirl_eq_sum_of_orthonormal _ e (fun g h => triAct12_mul ρ g h)
    (fun g => triAct12_inv ρ g) he_mem heorth hspan v

/-- **The (1,2) projector formula, Gram form** (conjugate twin). -/
theorem triTwirl12_eq_gram_sum {a : ℕ}
    (e : Fin a → (((Fin d × Fin d) × Fin d) → ℂ))
    (he_mem : ∀ i, e i ∈ triInvariant12 ρ)
    (hspan : triInvariant12 ρ
      ≤ Submodule.span ℂ (Set.range e))
    [Invertible (gramMat e)]
    (v : ((Fin d × Fin d) × Fin d) → ℂ) :
    triTwirl12 ρ *ᵥ v
      = ∑ α, ((gramMat e)⁻¹ *ᵥ (fun β => vecInner (e β) v)) α
          • e α :=
  avgTwirl_eq_gram_sum _ e (fun g h => triAct12_mul ρ g h)
    (fun g => triAct12_inv ρ g) he_mem hspan v

/-! ### Trace and the character formula for a(rho) -/

theorem triMat_trace (A B C : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (triMat A B C)
      = Matrix.trace A * Matrix.trace B * Matrix.trace C := by
  show (∑ p : (Fin d × Fin d) × Fin d, triMat A B C p p)
      = (∑ i, A i i) * (∑ j, B j j) * (∑ k, C k k)
  have hdiag : ∀ p : (Fin d × Fin d) × Fin d,
      triMat A B C p p
        = A p.1.1 p.1.1 * B p.1.2 p.1.2 * C p.2 p.2 :=
    fun p => triMat_apply A B C p p
  rw [Finset.sum_congr rfl (fun p _ => hdiag p), Fintype.sum_prod_type]
  have hC : ∀ x : Fin d × Fin d,
      (∑ k : Fin d, A x.1 x.1 * B x.2 x.2 * C k k)
        = (A x.1 x.1 * B x.2 x.2) * ∑ k : Fin d, C k k := by
    intro x
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => hC x), ← Finset.sum_mul]
  have hAB : (∑ x : Fin d × Fin d, A x.1 x.1 * B x.2 x.2)
      = (∑ i, A i i) * ∑ j, B j j :=
    sum_prod_mul (fun i => A i i) (fun j => B j j)
  rw [hAB]

theorem trace_orientConj (M : G → Matrix (Fin d) (Fin d) ℂ) (g : G) :
    Matrix.trace (orientConj M g) = star (Matrix.trace (M g)) := by
  show (∑ i, orientConj M g i i) = star (∑ i, M g i i)
  rw [star_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The trace of the (2,1) twirl is the character average
`(1/|G|) sum_g chi(g) chi(g) star (chi(g))` - the Clebsch-Gordan
multiplicity formula for a(rho), with the trace on the left
carrying the dimension (see the basis identities below). -/
theorem triTwirl21_trace_char :
    Matrix.trace (triTwirl21 ρ)
      = (Fintype.card G : ℂ)⁻¹ * ∑ g,
        Matrix.trace (repMatrix ρ g) * Matrix.trace (repMatrix ρ g)
          * star (Matrix.trace (repMatrix ρ g)) := by
  unfold triTwirl21
  rw [avgTwirl_trace]
  refine congrArg _ ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  show Matrix.trace (triMat (repMatrix ρ g) (repMatrix ρ g)
      (orientConj (repMatrix ρ) g)) = _
  rw [triMat_trace, trace_orientConj]

/-- The trace of the (1,2) twirl is the conjugate character
average. -/
theorem triTwirl12_trace_char :
    Matrix.trace (triTwirl12 ρ)
      = (Fintype.card G : ℂ)⁻¹ * ∑ g,
        Matrix.trace (repMatrix ρ g)
          * star (Matrix.trace (repMatrix ρ g))
          * star (Matrix.trace (repMatrix ρ g)) := by
  unfold triTwirl12
  rw [avgTwirl_trace]
  refine congrArg _ ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  show Matrix.trace (triMat (repMatrix ρ g)
      (orientConj (repMatrix ρ) g) (orientConj (repMatrix ρ) g)) = _
  rw [triMat_trace, trace_orientConj]

/-- **a(rho) as the character average.** For any chosen
orthonormal basis of the (2,1) invariant subspace indexed by
`Fin a`, the symbol `a` equals the (2,1) character average - the
Clebsch-Gordan multiplicity of rho in rho x rho, computed at
symbolic `a`. -/
theorem triDim21_char_average {a : ℕ}
    (e : Fin a → (((Fin d × Fin d) × Fin d) → ℂ))
    (he_mem : ∀ i, e i ∈ triInvariant21 ρ)
    (heorth : ∀ i j, vecInner (e i) (e j) = if i = j then 1 else 0)
    (hspan : triInvariant21 ρ
      ≤ Submodule.span ℂ (Set.range e)) :
    (a : ℂ) = (Fintype.card G : ℂ)⁻¹ * ∑ g,
        Matrix.trace (repMatrix ρ g) * Matrix.trace (repMatrix ρ g)
          * star (Matrix.trace (repMatrix ρ g)) := by
  rw [← triTwirl21_trace_char ρ]
  exact (avgTwirl_trace_eq_of_orthonormal _ e
    (fun g h => triAct21_mul ρ g h) (fun g => triAct21_inv ρ g)
    he_mem heorth hspan).symm

end TripleAction

/-! ## Seat instance (labeled): the trivial representation, a(rho) = 1

This section is a SANITY CHECK, not the general claim. At the
trivial representation (d = 1) the (2,1) action is trivial, the
invariant subspace is the whole (one-dimensional) tensor space,
a(rho) = 1 BY COMPUTATION, the twirl is the identity, and the
projector formula collapses to the scalar/line form - the
pair-twirl shape. Nothing above this section uses it. -/

section SeatInstance

variable {G : Type*} [Group G] [Fintype G]

theorem repMatrix_oneHom (g : G) :
    repMatrix (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) g = 1 := by
  simp [repMatrix]

theorem orientConj_repMatrix_oneHom (g : G) :
    orientConj (repMatrix (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)))
      g = 1 := by
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  rw [conjEntry, repMatrix_oneHom, Matrix.one_apply, if_pos rfl,
    star_one]

theorem triAct21_oneHom (g : G) :
    triAct21 (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) g = 1 := by
  unfold triAct21
  rw [repMatrix_oneHom, orientConj_repMatrix_oneHom, triMat_one]

theorem triInvariant21_oneHom :
    triInvariant21 (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) = ⊤ := by
  ext w
  simp only [triInvariant21, mem_avgInvariant, Submodule.mem_top,
    iff_true]
  intro h
  rw [triAct21_oneHom, Matrix.one_mulVec]

theorem triTwirl21_oneHom :
    triTwirl21 (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) = 1 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := cardG_ne_zero
  unfold triTwirl21
  rw [avgTwirl_def,
    Finset.sum_congr rfl (fun g _ => triAct21_oneHom g),
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem triDim21_oneHom :
    triDim21 (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) = 1 := by
  unfold triDim21
  rw [triInvariant21_oneHom, finrank_top,
    Module.finrank_pi]
  simp [Fintype.card_prod]

/-- The collapsed projector formula at the seat: with the single
unit invariant vector `e0 = fun _ => 1`, the twirl is
`v ↦ vecInner e0 v • e0` - the line form, as at the pair twirls. -/
theorem triTwirl21_oneHom_apply
    (v : ((Fin 1 × Fin 1) × Fin 1) → ℂ) :
    triTwirl21 (1 : G →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) *ᵥ v
      = vecInner (fun _ => (1 : ℂ)) v • (fun _ => (1 : ℂ)) := by
  have hvec : vecInner (fun _ => (1 : ℂ)) v = v ((0, 0), 0) := by
    rw [vecInner_apply]
    rw [Finset.sum_eq_single ((0, 0), 0)]
    · simp
    · intro q _ hq
      exact absurd (Subsingleton.elim q ((0, 0), 0)) hq
    · intro h
      exact absurd (Finset.mem_univ ((0, 0), 0)) h
  funext p
  have hp : p = ((0, 0), 0) := Subsingleton.elim p _
  rw [triTwirl21_oneHom, Matrix.one_mulVec, Pi.smul_apply, hvec, hp]
  simp

end SeatInstance

end ThetLogos
