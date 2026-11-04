import ThetLogos.Span3SeatSchurGateItem5
import ThetLogos.LayerKernelPos

/-!
# ThetLogos.PositivityPropagation — PROP-0 + PROP-1A: positivity
propagation through one factor-2 spatial blocking step

Lane build (positivity propagation package, commissioned by Jeff
2026-11-03 "run it", per the ratified scoping dossier
`positivity-propagation-scoping-2026-11-03.md`). Built in the
isolated worktree `~/workspace/thet-logos-prop`, branch
`prop-lane`, from main-tree HEAD `30eec70`. NOT integrated — the
parent runs the ceremony.

## What this module is

The scoping dossier's PROP-0 (definitions) and PROP-1A
(propagation at the `PosKernel` level), and nothing else:

* **PROP-0.** The blocked layer datum for one factor-2 spatial
  blocking step of the layer (`Even N → N/2`): the octet
  decomposition of the fine layer links over the coarse layer
  links (`layerOctetEquiv`), the blocked layer kernel
  `blockedLayerKernel` — the fiber integral of `𝒜` over the
  fibers of the layer block map, in the section (assembly)
  coordinates of `layerBlockAsm` — and the **pullback-pairing
  identity** `blockedLayerPairing_eq`: the coarse pairing of a
  coarse observable `F'` against the blocked kernel is the fine
  pairing of the pullback `F' ∘ layerBlockMap` against `𝒜`.
  No positivity is asserted in PROP-0.
* **PROP-1A.** The trivial direction, landed as bookkeeping so
  it is never later sold as the theorem:
  `LayerKernelPosAll μG ρ hρcont β → PosKernel
  (blockedLayerKernelFun …)`. The hypothesis
  `LayerKernelPosAll` is NAMED, NOT discharged — it is the
  positivity bridge's target (PB-1..PB-3, separate lane); this
  module proves the implication and nothing about the
  hypothesis.

## What this module is NOT

* NOT PROP-1B (propagation at the `LayerKernelPos` level):
  dominated by the bridge, deliberately not fired (scoping §5).
* NOT a form-preservation statement: the blocked kernel is
  **not** claimed to be a Wilson layer kernel at any coarse
  datum. The scoping's T2 probe (PROP-2-PROBE, run alongside
  this build) fired **K-PROP-FORM at the probe seat**: at
  `(N = 2, G = Multiplicative (ZMod 2), sign character)` the
  blocked kernel's diagonal is `(A'⁸ + B'⁸)³ ≠ 1` at every
  sampled `β ≠ 0`, while every Wilson layer kernel at the
  coarse seat has diagonal exactly `1`. The kernel-level form
  statement is dead at the miniature, as its measure-level
  sibling RG-1 already was in-tree. This module therefore
  carries the *general* blocked kernel, not a running `β'`.
* NOT a margin statement (PROP-3 is Stage 3c itself,
  research-scale, unpriced). The probe's margin ratio at the
  seat was exactly `1` (K-PROP-MARGIN did not fire at the
  miniature); that is a T2 seat computation, not a theorem,
  and nothing here depends on it.
* The T2 probes themselves live beside the scoping dossier,
  not in this module; every statement below is T1.

NO CLAIM; parts of the Clay statement closed: 0; dials 0/4.
Nothing here proves or refutes `LayerKernelPos`, FACT,
clause (a), or uniformity.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The octet decomposition of the layer (PROP-0, geometry)

One disclosed scheme, in the `BlockingScheme` pattern of
Stage 2: a coarse layer site is a doubled fine site; the eight
fine links of direction `ν` based at the eight fine sites of a
coarse site's `2×2×2` spatial block form the **octet** over the
coarse link `(coarse site, ν)`, and the blocked link value is
the ordered product of the octet (offsets in binary order).
The layer's time coordinate is untouched: blocking is spatial,
inside the layer. -/

section Octet

variable {N : ℕ} [NeZero N]

/-- `N / 2` is nonzero when `N` is even (and nonzero). -/
theorem neZero_half (hN : Even N) : NeZero (N / 2) :=
  ⟨by
    have h2 : 2 ≤ N := two_le_of_even hN
    omega⟩

/-- The octet index of a fine site: the three spatial parities
of the site, packed as bits `b₀ + 2b₁ + 4b₂`. -/
def layerOctetIndex (x : Fin 4 → ZMod N) : Fin 8 :=
  ⟨(x 1).val % 2 + 2 * ((x 2).val % 2) + 4 * ((x 3).val % 2), by
    have h1 : (x 1).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h2 : (x 2).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h3 : (x 3).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega⟩

/-- The coarse layer site under a fine layer site: halve every
coordinate (the time coordinate `0` stays `0`). -/
def layerCoarseSite (hN : Even N) (c : LayerSite N) : LayerSite (N / 2) :=
  ⟨fun j => (((c.1 j).val / 2 : ℕ) : ZMod (N / 2)), by
    have hlt : (c.1 0).val < N := ZMod.val_lt _
    obtain ⟨k, hk⟩ := hN
    show ((((c.1 0).val / 2 : ℕ) : ZMod (N / 2))).val = 0
    rw [ZMod.val_natCast_of_lt (show (c.1 0).val / 2 < N / 2 by omega),
      c.2]⟩

theorem layerCoarseSite_apply (hN : Even N) (c : LayerSite N) (j : Fin 4) :
    (layerCoarseSite hN c).1 j = (((c.1 j).val / 2 : ℕ) : ZMod (N / 2)) :=
  rfl

/-- The coarse layer link under a fine layer link: halve the
base site, keep the direction. -/
def layerCoarseLink (hN : Even N) (ℓ : LayerLink N) : LayerLink (N / 2) :=
  ⟨((layerCoarseSite hN ⟨ℓ.1.1, ℓ.2.1⟩).1, ℓ.1.2),
    (layerCoarseSite hN ⟨ℓ.1.1, ℓ.2.1⟩).2, ℓ.2.2⟩

/-- The fine site over a coarse layer site at octet offset `i`:
double the coarse coordinates and add the offset bits; the
time coordinate is `0`. -/
def layerFineSite (c : LayerSite (N / 2)) (i : Fin 8) :
    Fin 4 → ZMod N :=
  fun j => if j = 0 then 0
    else ((2 * (c.1 j).val + (i.val / 2 ^ (j.val - 1)) % 2 : ℕ) : ZMod N)

omit [NeZero N] in
theorem layerFineSite_zero (c : LayerSite (N / 2)) (i : Fin 8) :
    (layerFineSite c i 0).val = 0 := by
  show (if (0 : Fin 4) = 0 then (0 : ZMod N) else _).val = 0
  rw [ite_eq_left rfl]
  exact ZMod.val_zero

omit [NeZero N] in
theorem layerFineSite_apply_zero (c : LayerSite (N / 2)) (i : Fin 8) :
    layerFineSite c i 0 = 0 := by
  show (if (0 : Fin 4) = 0 then (0 : ZMod N) else _) = 0
  exact ite_eq_left rfl

theorem layerFineSite_val (hN : Even N) (c : LayerSite (N / 2))
    (i : Fin 8) {j : Fin 4} (hj : j ≠ 0) :
    (layerFineSite c i j).val
      = 2 * (c.1 j).val + (i.val / 2 ^ (j.val - 1)) % 2 := by
  have : NeZero (N / 2) := neZero_half hN
  have hlt : (c.1 j).val < N / 2 := ZMod.val_lt _
  have hbit : (i.val / 2 ^ (j.val - 1)) % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  obtain ⟨k, hk⟩ := hN
  show (if j = 0 then (0 : ZMod N) else _).val = _
  rw [ite_eq_right hj]
  exact ZMod.val_natCast_of_lt (by omega)

theorem layerCoarseSite_fineSite (hN : Even N) (c : LayerSite (N / 2))
    (i : Fin 8) :
    layerCoarseSite hN ⟨layerFineSite c i, layerFineSite_zero c i⟩ = c := by
  have : NeZero (N / 2) := neZero_half hN
  apply Subtype.ext
  funext j
  show (((layerFineSite c i j).val / 2 : ℕ) : ZMod (N / 2)) = _
  by_cases hj : j = 0
  · subst hj
    rw [layerFineSite_zero]
    show (((0 / 2 : ℕ)) : ZMod (N / 2)) = c.1 0
    rw [show ((0 / 2 : ℕ)) = 0 from rfl, Nat.cast_zero,
      ← ZMod.natCast_zmod_val (c.1 0), c.2, Nat.cast_zero]
  · rw [layerFineSite_val hN c i hj]
    have hbit : (i.val / 2 ^ (j.val - 1)) % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    have hdiv : (2 * (c.1 j).val + (i.val / 2 ^ (j.val - 1)) % 2) / 2
        = (c.1 j).val := by omega
    rw [hdiv, ZMod.natCast_zmod_val]

theorem layerOctetIndex_fineSite (hN : Even N) (c : LayerSite (N / 2))
    (i : Fin 8) :
    layerOctetIndex (layerFineSite c i) = i := by
  apply Fin.ext
  have hb : ∀ a : ℕ, ∀ j : Fin 4, j.val - 1 = a → j ≠ 0 →
      ((layerFineSite c i j).val) % 2 = (i.val / 2 ^ a) % 2 := by
    intro a j hj1 hj0
    rw [layerFineSite_val hN c i hj0, hj1]
    have hbl : (i.val / 2 ^ a) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have h1 := hb 0 1 (by rfl) (by norm_num)
  have h2 := hb 1 2 (by rfl) (by norm_num)
  have h3 := hb 2 3 (by rfl) (by norm_num)
  simp only [pow_zero, Nat.div_one] at h1
  have hi : i.val < 8 := i.2
  show (layerFineSite c i 1).val % 2
      + 2 * ((layerFineSite c i 2).val % 2)
      + 4 * ((layerFineSite c i 3).val % 2) = i.val
  rw [h1, h2, h3]
  have hb1 : (i.val / 2 ^ 0) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb2 : (i.val / 2 ^ 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb3 : (i.val / 2 ^ 2) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

theorem layerFineSite_coarse (hN : Even N) (x : Fin 4 → ZMod N)
    (hx : (x 0).val = 0) :
    layerFineSite (layerCoarseSite hN ⟨x, hx⟩) (layerOctetIndex x) = x := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [layerFineSite_apply_zero, ← ZMod.natCast_zmod_val (x 0), hx,
      Nat.cast_zero]
  · have hval := layerFineSite_val hN (layerCoarseSite hN ⟨x, hx⟩)
      (layerOctetIndex x) hj
    have hval2 : (layerFineSite (layerCoarseSite hN ⟨x, hx⟩)
        (layerOctetIndex x) j).val
        = 2 * (((((x j).val / 2 : ℕ) : ZMod (N / 2))).val)
          + ((layerOctetIndex x).val / 2 ^ (j.val - 1)) % 2 := hval
    have hlt : (x j).val < N := ZMod.val_lt _
    have hdivlt : (x j).val / 2 < N / 2 := by
      obtain ⟨k, hk⟩ := hN
      omega
    rw [ZMod.val_natCast_of_lt hdivlt] at hval2
    -- the bit of the packed index at axis `j.val - 1` is `(x j).val % 2`
    have hbit : ((layerOctetIndex x).val / 2 ^ (j.val - 1)) % 2
        = (x j).val % 2 := by
      have hb1 : (x 1).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hb2 : (x 2).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hb3 : (x 3).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hjv : j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
        have h4 : j.val < 4 := j.2
        have h0 : j.val ≠ 0 := by
          intro h
          apply hj
          exact Fin.ext (by simp [h])
        omega
      show ((x 1).val % 2 + 2 * ((x 2).val % 2) + 4 * ((x 3).val % 2))
          / 2 ^ (j.val - 1) % 2 = (x j).val % 2
      rcases hjv with h | h | h
      · have hj1 : j = 1 := Fin.ext h
        rw [hj1]
        show ((x 1).val % 2 + 2 * ((x 2).val % 2) + 4 * ((x 3).val % 2))
            / 1 % 2 = (x 1).val % 2
        omega
      · have hj2 : j = 2 := Fin.ext h
        rw [hj2]
        show ((x 1).val % 2 + 2 * ((x 2).val % 2) + 4 * ((x 3).val % 2))
            / 2 % 2 = (x 2).val % 2
        omega
      · have hj3 : j = 3 := Fin.ext h
        rw [hj3]
        show ((x 1).val % 2 + 2 * ((x 2).val % 2) + 4 * ((x 3).val % 2))
            / 4 % 2 = (x 3).val % 2
        omega
    rw [hbit] at hval2
    have hsum : 2 * ((x j).val / 2) + (x j).val % 2 = (x j).val := by
      have h := Nat.div_add_mod (x j).val 2
      omega
    calc layerFineSite (layerCoarseSite hN ⟨x, hx⟩) (layerOctetIndex x) j
        = ((layerFineSite (layerCoarseSite hN ⟨x, hx⟩)
            (layerOctetIndex x) j).val : ZMod N) :=
          (ZMod.natCast_zmod_val _).symm
      _ = ((x j).val : ZMod N) := by rw [hval2, hsum]
      _ = x j := ZMod.natCast_zmod_val _

/-- **The octet decomposition**: every fine layer link lies in
exactly one octet over exactly one coarse layer link — as an
equivalence `LayerLink N ≃ LayerLink (N/2) × Fin 8`. -/
def layerOctetEquiv (hN : Even N) :
    LayerLink N ≃ LayerLink (N / 2) × Fin 8 where
  toFun ℓ := (layerCoarseLink hN ℓ, layerOctetIndex ℓ.1.1)
  invFun p :=
    ⟨(layerFineSite (⟨p.1.1.1, p.1.2.1⟩ : LayerSite (N / 2)) p.2, p.1.1.2),
      layerFineSite_zero (⟨p.1.1.1, p.1.2.1⟩ : LayerSite (N / 2)) p.2,
      p.1.2.2⟩
  left_inv ℓ := by
    obtain ⟨⟨x, ν⟩, hx, hν⟩ := ℓ
    apply Subtype.ext
    show (layerFineSite (layerCoarseSite hN ⟨x, hx⟩) (layerOctetIndex x), ν)
      = (x, ν)
    rw [Prod.mk.injEq]
    exact ⟨layerFineSite_coarse hN x hx, rfl⟩
  right_inv p := by
    obtain ⟨⟨⟨y, ν⟩, hy, hν⟩, i⟩ := p
    show (layerCoarseLink hN
        ⟨(layerFineSite (⟨y, hy⟩ : LayerSite (N / 2)) i, ν),
          layerFineSite_zero (⟨y, hy⟩ : LayerSite (N / 2)) i, hν⟩,
      layerOctetIndex (layerFineSite (⟨y, hy⟩ : LayerSite (N / 2)) i))
      = (⟨(y, ν), hy, hν⟩, i)
    have h1 : layerCoarseLink hN
        ⟨(layerFineSite (⟨y, hy⟩ : LayerSite (N / 2)) i, ν),
          layerFineSite_zero (⟨y, hy⟩ : LayerSite (N / 2)) i, hν⟩
        = ⟨(y, ν), hy, hν⟩ := by
      apply Subtype.ext
      show ((layerCoarseSite hN
          ⟨layerFineSite (⟨y, hy⟩ : LayerSite (N / 2)) i,
            layerFineSite_zero _ i⟩).1, ν) = (y, ν)
      rw [Prod.mk.injEq]
      exact ⟨congrArg Subtype.val
        (layerCoarseSite_fineSite hN ⟨y, hy⟩ i), rfl⟩
    have h2 : layerOctetIndex
        (layerFineSite (⟨y, hy⟩ : LayerSite (N / 2)) i) = i :=
      layerOctetIndex_fineSite hN ⟨y, hy⟩ i
    rw [h1, h2]

end Octet

/-! ## §2. The block map and its assembly section (PROP-0, algebra)

The blocked link value of a fine configuration `u` at a coarse
link `ℓ'` is the ordered product of the octet of `u` over
`ℓ'`. The **assembly** `layerBlockAsm` is the disclosed
section of the block map: it rebuilds a fine configuration
from a coarse one `U` and fiber coordinates `w` (one tail
`Fin 7 → G` per coarse link) by putting the corrected head
`U ℓ' * (∏ tail)⁻¹` at offset `0` and the tail values at the
remaining offsets, so the octet product over `ℓ'` is exactly
`U ℓ'`. -/

section BlockAlgebra

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- The ordered product of an octet of link values: the head
times the product of the tail, in successor order (a `List`
product — the group is not assumed commutative). -/
def layerOctetProd (v : Fin 8 → G) : G :=
  v 0 * (List.ofFn (fun j : Fin 7 => v j.succ)).prod

/-- The assembled octet over a coarse link value `a` with
tail `t`: head corrected by the inverse tail product, so the
octet product is `a` again. -/
def layerOctetAsm (a : G) (t : Fin 7 → G) : Fin 8 → G :=
  Fin.cons (a * ((List.ofFn t).prod)⁻¹) t

theorem layerOctetProd_asm (a : G) (t : Fin 7 → G) :
    layerOctetProd (layerOctetAsm a t) = a := by
  have h0 : layerOctetAsm a t 0
      = a * ((List.ofFn t).prod)⁻¹ := Fin.cons_zero _ _
  have hprod : (List.ofFn (fun j => layerOctetAsm a t j.succ)).prod
      = (List.ofFn t).prod :=
    congrArg (fun f => (List.ofFn f).prod)
      (funext fun j => Fin.cons_succ _ _ j)
  show layerOctetAsm a t 0
      * (List.ofFn (fun j => layerOctetAsm a t j.succ)).prod = a
  rw [h0, hprod, mul_assoc, inv_mul_cancel, mul_one]

theorem layerOctetAsm_prod_tail (v : Fin 8 → G) :
    layerOctetAsm (layerOctetProd v) (fun j => v j.succ) = v := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · have h0 : layerOctetAsm (layerOctetProd v) (fun j => v j.succ) 0
        = layerOctetProd v
          * ((List.ofFn (fun j => v j.succ)).prod)⁻¹ :=
      Fin.cons_zero _ _
    rw [h0]
    exact mul_inv_cancel_right (v 0)
      ((List.ofFn (fun j => v j.succ)).prod)
  · have hs : layerOctetAsm (layerOctetProd v) (fun j => v j.succ)
        j.succ = (fun j => v j.succ) j := Fin.cons_succ _ _ j
    rw [hs]

/-- **The blocked layer datum**: the block map on layer
configurations for one factor-2 spatial blocking step —
at each coarse link, the ordered octet product. -/
def layerBlockMap (hN : Even N) (u : LayerLink N → G) :
    LayerLink (N / 2) → G :=
  fun ℓ' => layerOctetProd
    (fun i => u ((layerOctetEquiv hN).symm (ℓ', i)))

/-- The assembly section of the block map: the fine
configuration over a coarse configuration `U` with fiber
coordinates `w`. -/
def layerBlockAsm (hN : Even N) (U : LayerLink (N / 2) → G)
    (w : LayerLink (N / 2) → (Fin 7 → G)) : LayerLink N → G :=
  fun ℓ => layerOctetAsm (U ((layerOctetEquiv hN) ℓ).1)
    (w ((layerOctetEquiv hN) ℓ).1) ((layerOctetEquiv hN) ℓ).2

theorem layerBlockAsm_apply (hN : Even N) (U : LayerLink (N / 2) → G)
    (w : LayerLink (N / 2) → (Fin 7 → G)) (ℓ' : LayerLink (N / 2))
    (i : Fin 8) :
    layerBlockAsm hN U w ((layerOctetEquiv hN).symm (ℓ', i))
      = layerOctetAsm (U ℓ') (w ℓ') i := by
  show layerOctetAsm (U ((layerOctetEquiv hN)
      ((layerOctetEquiv hN).symm (ℓ', i))).1)
    (w ((layerOctetEquiv hN)
      ((layerOctetEquiv hN).symm (ℓ', i))).1)
    ((layerOctetEquiv hN)
      ((layerOctetEquiv hN).symm (ℓ', i))).2
    = layerOctetAsm (U ℓ') (w ℓ') i
  rw [Equiv.apply_symm_apply]

/-- The assembly is a section of the block map
(`layerBlockMap_asm`): blocking the assembled configuration
returns the coarse configuration. -/
theorem layerBlockMap_asm (hN : Even N) (U : LayerLink (N / 2) → G)
    (w : LayerLink (N / 2) → (Fin 7 → G)) :
    layerBlockMap hN (layerBlockAsm hN U w) = U := by
  funext ℓ'
  show layerOctetProd
      (fun i => layerBlockAsm hN U w
        ((layerOctetEquiv hN).symm (ℓ', i))) = U ℓ'
  rw [funext fun i => layerBlockAsm_apply hN U w ℓ' i]
  exact layerOctetProd_asm (U ℓ') (w ℓ')

/-- The assembly at the block of `u` with `u`'s own tails
rebuilds `u`: the fiber coordinates of a fine configuration
are its octet tails. -/
theorem layerBlockAsm_block (hN : Even N) (u : LayerLink N → G) :
    layerBlockAsm hN (layerBlockMap hN u)
        (fun ℓ' j => u ((layerOctetEquiv hN).symm (ℓ', j.succ)))
      = u := by
  funext ℓ
  have key := congrFun
    (layerOctetAsm_prod_tail
      (fun i => u ((layerOctetEquiv hN).symm
        ((layerOctetEquiv hN ℓ).1, i)))) ((layerOctetEquiv hN ℓ).2)
  simp only [Prod.eta, Equiv.symm_apply_apply] at key
  exact key

end BlockAlgebra

/-! ## §3. Measure transport for the assembly (PROP-0, measure)

The product (Haar) measure on layer configurations is pushed
around by the assembly coordinates: the assembly map
`layerBlockAsm` is measure-preserving from the product of
the coarse configuration measure and the fiber measure, and
the block map `layerBlockMap` is measure-preserving from the
fine configuration measure to the coarse one. The proofs
factor both maps through the corpus's pi-type transports
(`piCongrLeft`, `arrowProdEquivProdArrow`, pi maps), the
curry equivalence, and one rectangle computation: the octet
assembly corrects the head by a right translate, and the
measure is right-invariant. -/

section Transport

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] {N : ℕ} [NeZero N]

omit [MeasurableInv G] in
/-- The tail product `t ↦ (List.ofFn t).prod` is measurable,
for every fiber length (induction on the length: the head
times the product of the successor tail). -/
theorem measurable_listProd {n : ℕ} :
    Measurable (fun t : Fin n → G => (List.ofFn t).prod) := by
  induction n with
  | zero =>
    have h : (fun t : Fin 0 → G => (List.ofFn t).prod)
        = fun _ => 1 := by
      funext t
      simp [List.ofFn_zero]
    rw [h]
    exact measurable_const
  | succ n ih =>
    have h : (fun t : Fin (n + 1) → G => (List.ofFn t).prod)
        = fun t => t 0 * (List.ofFn (fun i => t i.succ)).prod := by
      funext t
      rw [List.ofFn_succ, List.prod_cons]
    rw [h]
    exact (measurable_pi_apply 0).mul
      (ih.comp (Measurable.of_eval fun i => measurable_pi_apply i.succ))

/-- Measurability of the octet assembly as a map on
`G × (Fin 7 → G)`. -/
theorem measurable_layerOctetAsm :
    Measurable (fun p : G × (Fin 7 → G) => layerOctetAsm p.1 p.2) := by
  refine Measurable.of_eval fun i => ?_
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · have h : (fun p : G × (Fin 7 → G) => layerOctetAsm p.1 p.2 0)
        = fun p => p.1 * ((List.ofFn p.2).prod)⁻¹ :=
      funext fun p => Fin.cons_zero _ _
    rw [h]
    exact measurable_fst.mul
      ((measurable_listProd.comp measurable_snd).inv)
  · have h : (fun p : G × (Fin 7 → G) => layerOctetAsm p.1 p.2 j.succ)
        = fun p => p.2 j :=
      funext fun p => Fin.cons_succ _ _ j
    rw [h]
    exact (measurable_pi_apply j).comp measurable_snd

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
/-- **The octet assembly is measure-preserving**: the pi
measure on `Fin 8 → G` is the pushforward of the product of
`μG` and the tail pi measure under the corrected-head
assembly. The head correction is a right translate, absorbed
by right invariance of `μG`. -/
theorem measurePreserving_layerOctetAsm :
    MeasurePreserving (fun p : G × (Fin 7 → G) =>
        layerOctetAsm p.1 p.2)
      (μG.prod (Measure.pi fun _ : Fin 7 => μG))
      (Measure.pi fun _ : Fin 8 => μG) := by
  refine ⟨measurable_layerOctetAsm, ?_⟩
  refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_layerOctetAsm
    (MeasurableSet.pi Set.countable_univ fun i _ => hs i)]
  -- the preimage of a pi rectangle under the assembly
  have hmem : ∀ (a : G) (t : Fin 7 → G),
      layerOctetAsm a t ∈ Set.univ.pi s
        ↔ a * ((List.ofFn t).prod)⁻¹ ∈ s 0 ∧ ∀ j, t j ∈ s j.succ := by
    intro a t
    have h0 : layerOctetAsm a t 0
        = a * ((List.ofFn t).prod)⁻¹ := Fin.cons_zero _ _
    have hsucc : ∀ j : Fin 7, layerOctetAsm a t j.succ = t j :=
      fun j => Fin.cons_succ _ _ j
    rw [Set.mem_pi]
    constructor
    · intro h
      refine ⟨?_, fun j => ?_⟩
      · have hh := h 0 (Set.mem_univ 0)
        rwa [h0] at hh
      · have hh := h j.succ (Set.mem_univ j.succ)
        rwa [hsucc j] at hh
    · intro h i _
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [h0]
        exact h.1
      · rw [hsucc j]
        exact h.2 j
  have hpre : (fun p : G × (Fin 7 → G) => layerOctetAsm p.1 p.2)
        ⁻¹' (Set.univ.pi s)
      = {p | p.1 * ((List.ofFn p.2).prod)⁻¹ ∈ s 0
          ∧ ∀ j, p.2 j ∈ s j.succ} := by
    ext ⟨a, t⟩
    exact hmem a t
  rw [hpre]
  have hmeas : MeasurableSet {p : G × (Fin 7 → G) |
      p.1 * ((List.ofFn p.2).prod)⁻¹ ∈ s 0
        ∧ ∀ j, p.2 j ∈ s j.succ} := by
    rw [← hpre]
    exact measurable_layerOctetAsm
      (MeasurableSet.pi Set.countable_univ fun i _ => hs i)
  rw [MeasureTheory.Measure.prod_apply_symm hmeas]
  -- the `a`-section over a fixed tail is a right translate of `s 0`
  have hsec : ∀ t : Fin 7 → G,
      μG ((fun a => (a, t)) ⁻¹' {p : G × (Fin 7 → G) |
        p.1 * ((List.ofFn p.2).prod)⁻¹ ∈ s 0
          ∧ ∀ j, p.2 j ∈ s j.succ})
      = (Set.univ.pi fun j => s j.succ).indicator
          (fun _ => μG (s 0)) t := by
    intro t
    by_cases ht : ∀ j, t j ∈ s j.succ
    · have hset : (fun a => (a, t)) ⁻¹' {p : G × (Fin 7 → G) |
          p.1 * ((List.ofFn p.2).prod)⁻¹ ∈ s 0
            ∧ ∀ j, p.2 j ∈ s j.succ}
        = (· * ((List.ofFn t).prod)⁻¹) ⁻¹' (s 0) := by
        ext a
        simp [ht]
      rw [hset, ← Measure.map_apply (measurable_mul_const _)
        (hs 0), MeasureTheory.map_mul_right_eq_self,
        Set.indicator_of_mem (show t ∈ Set.univ.pi (fun j => s j.succ)
          from Set.mem_pi.mpr fun j _ => ht j)]
    · have hset : (fun a => (a, t)) ⁻¹' {p : G × (Fin 7 → G) |
          p.1 * ((List.ofFn p.2).prod)⁻¹ ∈ s 0
            ∧ ∀ j, p.2 j ∈ s j.succ} = ∅ := by
        ext a
        simp [ht]
      rw [hset, MeasureTheory.measure_empty,
        Set.indicator_of_notMem]
      exact fun h => ht (fun j => h j (Set.mem_univ j))
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hsec),
    MeasureTheory.lintegral_indicator_const
      (MeasurableSet.pi Set.countable_univ fun j _ => hs j.succ) _,
    MeasureTheory.Measure.pi_pi]
  exact (Fin.prod_univ_succ (fun i => μG (s i))).symm

/-- The curry equivalence between functions on the product
index type `LayerLink (N/2) × Fin 8` and curried functions
(built by hand: this Mathlib pin has no `Equiv.prodCurry`). -/
def layerCurryEquiv :
    (LayerLink (N / 2) → (Fin 8 → G)) ≃ᵐ
      ((LayerLink (N / 2) × Fin 8) → G) where
  toFun z := fun p => z p.1 p.2
  invFun v := fun ℓ' i => v (ℓ', i)
  left_inv _z := rfl
  right_inv _v := rfl
  measurable_toFun :=
    Measurable.of_eval fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  measurable_invFun :=
    Measurable.of_eval fun ℓ' =>
      Measurable.of_eval fun i => measurable_pi_apply (ℓ', i)

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] [NeZero N] in
theorem layerCurryEquiv_apply (z : LayerLink (N / 2) → (Fin 8 → G))
    (p : LayerLink (N / 2) × Fin 8) :
    layerCurryEquiv z p = z p.1 p.2 := rfl

omit [Group G] [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant] [NeZero N] in
/-- **Uncurrying is measure-preserving** between the iterated
pi measure and the product-index pi measure (a `pi_eq`
rectangle computation: both sides are the double product of
the coordinate measures). -/
theorem measurePreserving_layerUncurry [NeZero (N / 2)] :
    MeasurePreserving (layerCurryEquiv (G := G))
      (Measure.pi fun _ : LayerLink (N / 2) =>
        (Measure.pi fun _ : Fin 8 => μG))
      (Measure.pi fun _ : (LayerLink (N / 2) × Fin 8) => μG) := by
  classical
  refine ⟨(layerCurryEquiv (G := G)).measurable, ?_⟩
  refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (layerCurryEquiv (G := G)).measurable
    (MeasurableSet.pi Set.countable_univ fun i _ => hs i)]
  have hpre : (layerCurryEquiv (G := G)) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun ℓ' => Set.univ.pi (fun i => s (ℓ', i))) := by
    ext z
    simp only [layerCurryEquiv_apply, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies]
    exact Prod.forall
  rw [hpre]
  trans ∏ ℓ', ∏ i : Fin 8, μG (s (ℓ', i))
  · rw [MeasureTheory.Measure.pi_pi]
    exact Finset.prod_congr rfl fun ℓ' _ =>
      MeasureTheory.Measure.pi_pi (fun _ : Fin 8 => μG)
        (fun i => s (ℓ', i))
  · exact (Fintype.prod_prod_type
      fun p : LayerLink (N / 2) × Fin 8 => μG (s p)).symm

omit [MeasurableInv G] [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
/-- **The shear is measure-preserving**: multiplying the
head coordinate by a tail-dependent group element preserves
the product measure (right invariance, rectangle by
rectangle). -/
theorem measurePreserving_octetShear :
    MeasurePreserving (fun p : G × (Fin 7 → G) =>
        (p.1 * (List.ofFn p.2).prod, p.2))
      (μG.prod (Measure.pi fun _ : Fin 7 => μG))
      (μG.prod (Measure.pi fun _ : Fin 7 => μG)) := by
  have hmeasf : Measurable (fun p : G × (Fin 7 → G) =>
      (p.1 * (List.ofFn p.2).prod, p.2)) :=
    (measurable_fst.mul
      (measurable_listProd.comp measurable_snd)).prodMk measurable_snd
  refine ⟨hmeasf, ?_⟩
  refine (MeasureTheory.Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hmeasf (MeasurableSet.prod hs ht)]
  have hpre : (fun p : G × (Fin 7 → G) =>
        (p.1 * (List.ofFn p.2).prod, p.2)) ⁻¹' (s ×ˢ t)
      = {p | p.1 * (List.ofFn p.2).prod ∈ s ∧ p.2 ∈ t} := rfl
  rw [hpre]
  have hmeas : MeasurableSet {p : G × (Fin 7 → G) |
      p.1 * (List.ofFn p.2).prod ∈ s ∧ p.2 ∈ t} := by
    rw [← hpre]
    exact hmeasf (MeasurableSet.prod hs ht)
  rw [MeasureTheory.Measure.prod_apply_symm hmeas]
  have hsec : ∀ u : Fin 7 → G,
      μG ((fun a => (a, u)) ⁻¹' {p : G × (Fin 7 → G) |
        p.1 * (List.ofFn p.2).prod ∈ s ∧ p.2 ∈ t})
      = t.indicator (fun _ => μG s) u := by
    intro u
    by_cases hu : u ∈ t
    · rw [Set.indicator_of_mem hu]
      have hset : (fun a => (a, u)) ⁻¹' {p : G × (Fin 7 → G) |
          p.1 * (List.ofFn p.2).prod ∈ s ∧ p.2 ∈ t}
        = (· * (List.ofFn u).prod) ⁻¹' s := by
        ext a
        simp [hu]
      rw [hset, ← Measure.map_apply (measurable_mul_const _) hs,
        MeasureTheory.map_mul_right_eq_self]
    · rw [Set.indicator_of_notMem hu]
      have hset : (fun a => (a, u)) ⁻¹' {p : G × (Fin 7 → G) |
          p.1 * (List.ofFn p.2).prod ∈ s ∧ p.2 ∈ t} = ∅ := by
        ext a
        simp [hu]
      rw [hset, MeasureTheory.measure_empty]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hsec),
    MeasureTheory.lintegral_indicator_const ht _]

/-- The octet split of a fine octet value: its blocked value
(the octet product) and its fiber coordinates (the tail). -/
def layerOctetSplit (v : Fin 8 → G) : G × (Fin 7 → G) :=
  (layerOctetProd v, fun j => v j.succ)

omit [MeasurableInv G] [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
/-- **The octet split is measure-preserving**: it is the
`Fin.succAbove` coordinate split followed by the shear. -/
theorem measurePreserving_layerOctetSplit :
    MeasurePreserving (layerOctetSplit (G := G))
      (Measure.pi fun _ : Fin 8 => μG)
      (μG.prod (Measure.pi fun _ : Fin 7 => μG)) := by
  have hfun : layerOctetSplit (G := G)
      = (fun p : G × (Fin 7 → G) => (p.1 * (List.ofFn p.2).prod, p.2))
        ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => G) 0) := by
    funext v
    show (layerOctetProd v, fun j => v j.succ)
      = (v 0 * (List.ofFn (fun j => v (Fin.succAbove 0 j))).prod,
          fun j => v (Fin.succAbove 0 j))
    rw [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · show v 0 * (List.ofFn (fun j => v j.succ)).prod
        = v 0 * (List.ofFn (fun j => v (Fin.succAbove 0 j))).prod
      rw [show (fun j => v (Fin.succAbove 0 j)) = (fun j => v j.succ)
        from funext fun j => congrArg v (congrFun Fin.succAbove_zero j)]
    · exact funext fun j =>
        (congrArg v (congrFun Fin.succAbove_zero j)).symm
  rw [hfun]
  exact (measurePreserving_octetShear μG).comp
    (measurePreserving_piFinSuccAbove (fun _ => μG) 0)

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] [NeZero N] in
/-- **The assembly is measure-preserving**: the fine layer
configuration measure is the pushforward of the product of
the coarse configuration measure and the fiber measure
under `layerBlockAsm`. Factorized as: arrow-prod commutation,
the pi map of the octet assembly, uncurrying, and the
`piCongrLeft` pullback along the octet equivalence. -/
theorem arrowProdEquivProdArrow_symm_apply
    (p : (LayerLink (N / 2) → G)
      × (LayerLink (N / 2) → (Fin 7 → G))) (ℓ' : LayerLink (N / 2)) :
    (MeasurableEquiv.arrowProdEquivProdArrow G (Fin 7 → G)
      (LayerLink (N / 2))).symm p ℓ' = (p.1 ℓ', p.2 ℓ') := rfl

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] in
theorem piCongrLeft_symm_apply_octet (hN : Even N)
    (v : (LayerLink (N / 2) × Fin 8) → G) (ℓ : LayerLink N) :
    ((MeasurableEquiv.piCongrLeft
      (fun _ : (LayerLink (N / 2) × Fin 8) => G)
      (layerOctetEquiv hN)).symm) v ℓ
      = v ((layerOctetEquiv hN) ℓ) := rfl

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
theorem measurePreserving_layerBlockAsm (hN : Even N)
    [NeZero (N / 2)] :
    MeasurePreserving (fun p : (LayerLink (N / 2) → G)
          × (LayerLink (N / 2) → (Fin 7 → G)) =>
        layerBlockAsm hN p.1 p.2)
      ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)))
      (Measure.pi fun _ : LayerLink N => μG) := by
  have hfun : (fun p : (LayerLink (N / 2) → G)
          × (LayerLink (N / 2) → (Fin 7 → G)) =>
        layerBlockAsm hN p.1 p.2)
      = ⇑(MeasurableEquiv.piCongrLeft
          (fun _ : (LayerLink (N / 2) × Fin 8) => G)
          (layerOctetEquiv hN)).symm
        ∘ ⇑(layerCurryEquiv (G := G))
        ∘ (fun z : LayerLink (N / 2) → (G × (Fin 7 → G)) =>
            fun ℓ' => layerOctetAsm (z ℓ').1 (z ℓ').2)
        ∘ ⇑(MeasurableEquiv.arrowProdEquivProdArrow G (Fin 7 → G)
            (LayerLink (N / 2))).symm := by
    funext ⟨U, w⟩ ℓ
    simp only [Function.comp_apply, layerCurryEquiv_apply,
      arrowProdEquivProdArrow_symm_apply,
      piCongrLeft_symm_apply_octet, layerBlockAsm]
  rw [hfun]
  exact ((MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : (LayerLink (N / 2) × Fin 8) => G)
        (layerOctetEquiv hN))
      (measurePreserving_piCongrLeft
        (fun _ : (LayerLink (N / 2) × Fin 8) => μG)
        (layerOctetEquiv hN))).comp
    ((measurePreserving_layerUncurry μG).comp
      ((measurePreserving_pi
          (fun _ : LayerLink (N / 2) =>
            μG.prod (Measure.pi fun _ : Fin 7 => μG))
          (fun _ : LayerLink (N / 2) =>
            Measure.pi fun _ : Fin 8 => μG)
          (fun _ => measurePreserving_layerOctetAsm μG)).comp
        (MeasurePreserving.symm
          (MeasurableEquiv.arrowProdEquivProdArrow G (Fin 7 → G)
            (LayerLink (N / 2)))
          (measurePreserving_arrowProdEquivProdArrow G (Fin 7 → G)
            (LayerLink (N / 2)) (fun _ => μG)
            (fun _ => Measure.pi fun _ : Fin 7 => μG))))))

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] in
/-- **The block map is measure-preserving**: the coarse
layer configuration measure is the pushforward of the fine
one under `layerBlockMap`. Factorized as the `piCongrLeft`
pullback along the octet equivalence, currying, the pi map
of the octet split, arrow-prod commutation, and the first
projection. -/
theorem piCongrLeft_symm_apply_octetSymm (hN : Even N)
    (u : LayerLink N → G) (p : LayerLink (N / 2) × Fin 8) :
    ((MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G)
      (layerOctetEquiv hN).symm).symm) u p
      = u ((layerOctetEquiv hN).symm p) := rfl

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] [NeZero N] in
theorem layerCurryEquiv_symm_apply
    (v : (LayerLink (N / 2) × Fin 8) → G) (ℓ' : LayerLink (N / 2))
    (i : Fin 8) :
    (layerCurryEquiv (G := G)).symm v ℓ' i = v (ℓ', i) := rfl

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] [NeZero N] in
theorem layerCurryEquiv_symm_apply_fun
    (v : (LayerLink (N / 2) × Fin 8) → G) (ℓ' : LayerLink (N / 2)) :
    (layerCurryEquiv (G := G)).symm v ℓ'
      = fun i => v (ℓ', i) := rfl

omit [Group G] [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [SecondCountableTopology G] [NeZero N] in
theorem arrowProdEquivProdArrow_fst_apply
    (z : LayerLink (N / 2) → (G × (Fin 7 → G))) (ℓ' : LayerLink (N / 2)) :
    ((MeasurableEquiv.arrowProdEquivProdArrow G (Fin 7 → G)
      (LayerLink (N / 2))) z).1 ℓ' = (z ℓ').1 := rfl

omit [MeasurableInv G] [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
theorem measurePreserving_layerBlockMap (hN : Even N)
    [NeZero (N / 2)] :
    MeasurePreserving (layerBlockMap hN)
      (Measure.pi fun _ : LayerLink N => μG)
      (Measure.pi fun _ : LayerLink (N / 2) => μG) := by
  have hfun : layerBlockMap hN
      = Prod.fst
        ∘ (⇑(MeasurableEquiv.arrowProdEquivProdArrow G (Fin 7 → G)
            (LayerLink (N / 2)))
          ∘ (fun z : LayerLink (N / 2) → (Fin 8 → G) =>
              fun ℓ' => layerOctetSplit (z ℓ'))
          ∘ ⇑(layerCurryEquiv (G := G)).symm
          ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G)
              (layerOctetEquiv hN).symm).symm) := by
    funext u ℓ'
    simp only [Function.comp_apply, layerCurryEquiv_symm_apply_fun,
      piCongrLeft_symm_apply_octetSymm,
      arrowProdEquivProdArrow_fst_apply, layerOctetSplit,
      layerBlockMap]
  rw [hfun]
  exact MeasureTheory.measurePreserving_fst.comp
    ((measurePreserving_arrowProdEquivProdArrow G (Fin 7 → G)
        (LayerLink (N / 2)) (fun _ => μG)
        (fun _ => Measure.pi fun _ : Fin 7 => μG)).comp
      ((measurePreserving_pi
          (fun _ : LayerLink (N / 2) =>
            Measure.pi fun _ : Fin 8 => μG)
          (fun _ : LayerLink (N / 2) =>
            μG.prod (Measure.pi fun _ : Fin 7 => μG))
          (fun _ => measurePreserving_layerOctetSplit μG)).comp
        ((MeasurePreserving.symm (layerCurryEquiv (G := G))
            (measurePreserving_layerUncurry μG)).comp
          (MeasurePreserving.symm
            (MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G)
              (layerOctetEquiv hN).symm)
            (measurePreserving_piCongrLeft
              (fun _ : LayerLink N => μG)
              (layerOctetEquiv hN).symm)))))

end Transport

/-! ## §4 Kernel: the blocked kernel and its `MemLp` datum

The fiber-integrated blocked kernel: the fine layer kernel
averaged over the assembly fiber, as a Bochner integral over
the product fiber measure (the iterated form agrees with it
by Fubini wherever the pairing identity needs it). -/

section Kernel

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The fiber-integrated blocked layer kernel at coarse
datum `(U, U')`: the fine layer kernel of the assembled
configurations, averaged over the product assembly fiber.
A datum of the coarse theory in its own right; by
K-PROP-FORM (fired at T2 by PROP-2-PROBE at the RG-1 seat)
it is not, in general, the layer kernel of any coarse
Wilson datum. -/
noncomputable def blockedLayerKernel (hN : Even N) [NeZero (N / 2)]
    (β : ℝ) (U U' : LayerLink (N / 2) → G) : ℂ :=
  ∫ q, layerKernel μG ρ β (layerBlockAsm hN U q.1)
      (layerBlockAsm hN U' q.2)
    ∂((Measure.pi fun _ : LayerLink (N / 2) =>
        (Measure.pi fun _ : Fin 7 => μG)).prod
      (Measure.pi fun _ : LayerLink (N / 2) =>
        (Measure.pi fun _ : Fin 7 => μG)))

/-- The blocked layer kernel as a kernel on pairs of coarse
configurations. -/
noncomputable def blockedLayerKernelFun (hN : Even N) [NeZero (N / 2)]
    (β : ℝ) : (LayerLink (N / 2) → G) × (LayerLink (N / 2) → G) → ℂ :=
  fun p => blockedLayerKernel μG ρ hN β p.1 p.2

/-- The blocked-kernel integrand on (coarse pair) × (fiber
pair): the fine layer kernel of the two assembled
configurations. -/
noncomputable def blockedLayerKernelIntegrand (hN : Even N) (β : ℝ) :
    ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → G)) ×
      ((LayerLink (N / 2) → (Fin 7 → G)) ×
        (LayerLink (N / 2) → (Fin 7 → G))) → ℂ :=
  fun r => layerKernel μG ρ β (layerBlockAsm hN r.1.1 r.2.1)
    (layerBlockAsm hN r.1.2 r.2.2)

/-- The assembly pullback of the fine layer kernel: the fine
kernel read on assembled configurations, as a function on
pairs of (coarse configuration, fiber) points. -/
noncomputable def blockedLayerKernelPullback (hN : Even N) (β : ℝ) :
    ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ×
      ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) → ℂ :=
  fun q => layerKernel μG ρ β (layerBlockAsm hN q.1.1 q.1.2)
    (layerBlockAsm hN q.2.1 q.2.2)

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- The pullback is the integrand read through the
middle-exchange regrouping. -/
theorem blockedLayerKernelPullback_apply (hN : Even N) (β : ℝ)
    (q : ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ×
      ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G)))) :
    blockedLayerKernelPullback μG ρ hN β q
      = blockedLayerKernelIntegrand μG ρ hN β
          ((q.1.1, q.2.1), (q.1.2, q.2.2)) := rfl

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
include μG in
/-- The assembly, as a function of the coarse configuration
and the fiber jointly, is measurable (it is
measure-preserving, §3). -/
theorem measurable_layerBlockAsm_pair (hN : Even N) [NeZero (N / 2)] :
    Measurable (fun p : (LayerLink (N / 2) → G)
        × (LayerLink (N / 2) → (Fin 7 → G)) =>
      layerBlockAsm hN p.1 p.2) :=
  (measurePreserving_layerBlockAsm μG hN).measurable

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
include μG in
/-- Joint measurability of the Boltzmann factor in the
stratum and the two assembled configurations (the corpus's
`measurable_layerAction` input, composed with the assembly
regrouping at the (coarse pair) × (fiber pair) grouping). -/
theorem measurable_boltzmann_blockedIntegrand (hN : Even N)
    [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable ((fun q : (LayerSite N → G) × (LayerLink N → G)
          × (LayerLink N → G) =>
        (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
      (fun q :
        (((LayerLink (N / 2) → G) × (LayerLink (N / 2) → G)) ×
          ((LayerLink (N / 2) → (Fin 7 → G)) ×
            (LayerLink (N / 2) → (Fin 7 → G)))) × (LayerSite N → G) =>
        (q.2, layerBlockAsm hN q.1.1.1 q.1.2.1,
          layerBlockAsm hN q.1.1.2 q.1.2.2))) := by
  classical
  have hAsm : Measurable (fun q :
      (((LayerLink (N / 2) → G) × (LayerLink (N / 2) → G)) ×
        ((LayerLink (N / 2) → (Fin 7 → G)) ×
          (LayerLink (N / 2) → (Fin 7 → G)))) × (LayerSite N → G) =>
      (q.2, layerBlockAsm hN q.1.1.1 q.1.2.1,
        layerBlockAsm hN q.1.1.2 q.1.2.2)) :=
    measurable_snd.prodMk
      (((measurable_layerBlockAsm_pair μG hN).comp
        ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_fst.comp
            (measurable_snd.comp measurable_fst)))).prodMk
        ((measurable_layerBlockAsm_pair μG hN).comp
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
            (measurable_snd.comp
              (measurable_snd.comp measurable_fst)))))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  exact h1.comp hAsm

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
/-- The blocked-kernel integrand is almost-everywhere
strongly measurable on the (coarse pair) × (fiber pair)
product space. -/
theorem blockedLayerKernelIntegrand_aestronglyMeasurable
    (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    AEStronglyMeasurable (blockedLayerKernelIntegrand μG ρ hN β)
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) := by
  classical
  have hA := (measurable_boltzmann_blockedIntegrand μG ρ hN hρcont β).aestronglyMeasurable.integral_prod_right'
    (μ := ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
      ((Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))))
    (ν := Measure.pi fun _ : LayerSite N => μG)
  exact hA.congr (ae_of_all _ fun r => rfl)

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
include μG in
/-- Joint measurability of the Boltzmann factor in the
stratum and the two assembled configurations, at the
(coarse, fiber) × (coarse, fiber) grouping of the
pullback. -/
theorem measurable_boltzmann_blockedPullback (hN : Even N)
    [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable ((fun q : (LayerSite N → G) × (LayerLink N → G)
          × (LayerLink N → G) =>
        (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
      (fun q :
        (((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ×
          ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))))
          × (LayerSite N → G) =>
        (q.2, layerBlockAsm hN q.1.1.1 q.1.1.2,
          layerBlockAsm hN q.1.2.1 q.1.2.2))) := by
  classical
  have hAsm : Measurable (fun q :
      (((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ×
        ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))))
        × (LayerSite N → G) =>
      (q.2, layerBlockAsm hN q.1.1.1 q.1.1.2,
        layerBlockAsm hN q.1.2.1 q.1.2.2)) :=
    measurable_snd.prodMk
      (((measurable_layerBlockAsm_pair μG hN).comp
        ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp
            (measurable_fst.comp measurable_fst)))).prodMk
        ((measurable_layerBlockAsm_pair μG hN).comp
          ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
            (measurable_snd.comp
              (measurable_snd.comp measurable_fst)))))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  exact h1.comp hAsm

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
/-- The assembly pullback of the fine layer kernel is
almost-everywhere strongly measurable. -/
theorem blockedLayerKernelPullback_aestronglyMeasurable
    (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    AEStronglyMeasurable (blockedLayerKernelPullback μG ρ hN β)
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) := by
  classical
  have hA := (measurable_boltzmann_blockedPullback μG ρ hN hρcont β).aestronglyMeasurable.integral_prod_right'
    (μ := ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))).prod
      ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))))
    (ν := Measure.pi fun _ : LayerSite N => μG)
  exact hA.congr (ae_of_all _ fun q => rfl)

omit [μG.IsMulLeftInvariant] [μG.IsInvInvariant] in
/-- At a frozen coarse pair, the blocked-kernel integrand
is almost-everywhere strongly measurable in the fiber
pair (a section of a jointly measurable Boltzmann factor
is measurable). -/
theorem blockedLayerKernelIntegrand_section_aestronglyMeasurable
    (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (p : (LayerLink (N / 2) → G) × (LayerLink (N / 2) → G)) :
    AEStronglyMeasurable
      (fun q => blockedLayerKernelIntegrand μG ρ hN β (p, q))
      ((Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))) := by
  classical
  have hM : Measurable ((fun q : (LayerSite N → G)
          × (LayerLink N → G) × (LayerLink N → G) =>
        (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
      (fun q :
        ((LayerLink (N / 2) → (Fin 7 → G)) ×
          (LayerLink (N / 2) → (Fin 7 → G))) × (LayerSite N → G) =>
        (q.2, layerBlockAsm hN p.1 q.1.1,
          layerBlockAsm hN p.2 q.1.2))) := by
    have hAsm : Measurable (fun q :
        ((LayerLink (N / 2) → (Fin 7 → G)) ×
          (LayerLink (N / 2) → (Fin 7 → G))) × (LayerSite N → G) =>
        (q.2, layerBlockAsm hN p.1 q.1.1,
          layerBlockAsm hN p.2 q.1.2)) :=
      measurable_snd.prodMk
        (((measurable_layerBlockAsm_pair μG hN).comp
          (measurable_const.prodMk
            (measurable_fst.comp measurable_fst))).prodMk
          ((measurable_layerBlockAsm_pair μG hN).comp
            (measurable_const.prodMk
              (measurable_snd.comp measurable_fst))))
    have h1 : Measurable (fun q : (LayerSite N → G)
          × (LayerLink N → G) × (LayerLink N → G) =>
        (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
      Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp
          ((measurable_layerAction ρ hρcont β).neg))
    exact h1.comp hAsm
  have hA := hM.aestronglyMeasurable.integral_prod_right'
    (μ := (Measure.pi fun _ : LayerLink (N / 2) =>
        (Measure.pi fun _ : Fin 7 => μG)).prod
      (Measure.pi fun _ : LayerLink (N / 2) =>
        (Measure.pi fun _ : Fin 7 => μG)))
    (ν := Measure.pi fun _ : LayerSite N => μG)
  exact hA.congr (ae_of_all _ fun q => rfl)

/-- The assembly pullback of the fine layer kernel is
integrable on the (coarse, fiber) pair space (bounded by
`exp (|β| * layerBoundConst N)`, by
`layerKernel_norm_le`). -/
theorem blockedLayerKernelPullback_integrable
    (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Integrable (blockedLayerKernelPullback μG ρ hN β)
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) :=
  Integrable.of_bound
    (blockedLayerKernelPullback_aestronglyMeasurable μG ρ hN hρcont β)
    (Real.exp (|β| * layerBoundConst N))
    (ae_of_all _ fun q => by
      exact layerKernel_norm_le μG ρ β _ _)

/-- **PROP-0, the `MemLp` datum.** The blocked layer kernel
is `MemLp 2` on the coarse product space, under the same
representation-regularity hypothesis as the fine kernel's
`layerKernelFun_memLp`. -/
theorem blockedLayerKernelFun_memLp (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    MemLp (blockedLayerKernelFun μG ρ hN β) 2
      ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) => μG)) := by
  refine MemLp.of_bound ?_ (Real.exp (|β| * layerBoundConst N))
    (ae_of_all _ fun p => ?_)
  · have hA := (blockedLayerKernelIntegrand_aestronglyMeasurable
        μG ρ hN hρcont β).integral_prod_right'
      (μ := (Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) => μG))
      (ν := (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)))
    exact hA.congr (ae_of_all _ fun p => rfl)
  · have hInt : Integrable
        (fun q => blockedLayerKernelIntegrand μG ρ hN β (p, q))
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))) :=
      Integrable.of_bound
        (blockedLayerKernelIntegrand_section_aestronglyMeasurable
          μG ρ hN hρcont β p) (Real.exp (|β| * layerBoundConst N))
        (ae_of_all _ fun q => by
          exact layerKernel_norm_le μG ρ β _ _)
    calc ‖blockedLayerKernelFun μG ρ hN β p‖
        = ‖∫ q, blockedLayerKernelIntegrand μG ρ hN β (p, q)
            ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)).prod
              (Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)))‖ := rfl
      _ ≤ ∫ q, ‖blockedLayerKernelIntegrand μG ρ hN β (p, q)‖
            ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)).prod
              (Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG))) :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ _, (Real.exp (|β| * layerBoundConst N) : ℝ)
            ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)).prod
              (Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG))) :=
          MeasureTheory.integral_mono hInt.norm (integrable_const _)
            (fun q => by exact layerKernel_norm_le μG ρ β _ _)
      _ = Real.exp (|β| * layerBoundConst N) := by simp

/-- The middle-exchange regrouping
`((c, w), (c', w')) ↦ ((c, c'), (w, w'))` between the two
bracketings of the coarse/fiber four-fold product. -/
def layerBlockProdComm :
    ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ×
      ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ≃ᵐ
    ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → G)) ×
      ((LayerLink (N / 2) → (Fin 7 → G)) ×
        (LayerLink (N / 2) → (Fin 7 → G))) where
  toFun := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
  invFun := fun r => ((r.1.1, r.2.1), (r.1.2, r.2.2))
  left_inv := fun _q => rfl
  right_inv := fun _r => rfl
  measurable_toFun :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
  measurable_invFun :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))

omit [Group G] [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant] [NeZero N] in
/-- The middle-exchange regrouping is measure-preserving
between the two bracketings of the coarse/fiber four-fold
product (rectangle computation through `Measure.prod_eq`:
a section of the preimage of a rectangle is a rectangle of
sections). -/
theorem measurePreserving_layerBlockProdComm [NeZero (N / 2)] :
    MeasurePreserving (layerBlockProdComm (G := G) (N := N))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) := by
  classical
  refine ⟨(layerBlockProdComm (G := G) (N := N)).measurable, ?_⟩
  refine (MeasureTheory.Measure.prod_eq ?_).symm
  intro s t hs ht
  have hmeas : MeasurableSet
      ((layerBlockProdComm (G := G) (N := N)) ⁻¹' (s ×ˢ t)) :=
    (layerBlockProdComm (G := G) (N := N)).measurable (hs.prod ht)
  rw [MeasureTheory.Measure.map_apply
      (layerBlockProdComm (G := G) (N := N)).measurable (hs.prod ht),
    MeasureTheory.Measure.prod_apply hmeas]
  have hsec : ∀ z : (LayerLink (N / 2) → G)
        × (LayerLink (N / 2) → (Fin 7 → G)),
      (Prod.mk z) ⁻¹'
          ((layerBlockProdComm (G := G) (N := N)) ⁻¹' (s ×ˢ t))
        = ((Prod.mk z.1) ⁻¹' s) ×ˢ ((Prod.mk z.2) ⁻¹' t) :=
    fun z => rfl
  rw [MeasureTheory.lintegral_congr
    (fun z => by rw [hsec z, MeasureTheory.Measure.prod_prod])]
  -- the integrand factors as `A z.1 * B z.2`; split the
  -- lintegral over the (coarse, fiber) product
  rw [MeasureTheory.lintegral_prod_mul
      (f := fun U : LayerLink (N / 2) → G =>
        (Measure.pi fun _ : LayerLink (N / 2) => μG) ((Prod.mk U) ⁻¹' s))
      (g := fun w : LayerLink (N / 2) → (Fin 7 → G) =>
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)) ((Prod.mk w) ⁻¹' t))
      (measurable_measure_prodMk_left
        (ν := Measure.pi fun _ : LayerLink (N / 2) => μG) hs).aemeasurable
      (measurable_measure_prodMk_left
        (ν := Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)) ht).aemeasurable,
    ← MeasureTheory.Measure.prod_apply hs,
    ← MeasureTheory.Measure.prod_apply ht]

end Kernel

/-! ## §5 Pairing: the pullback-pairing identity (PROP-0)
and one-step positivity propagation (PROP-1A) -/

section Pairing

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The pairing integrand of the blocked kernel, at the
(coarse, fiber) × (coarse, fiber) grouping: the pulled-back
fine kernel against the coarse observable read at the two
block values. -/
noncomputable def blockedPairingIntegrand (hN : Even N) [NeZero (N / 2)] (β : ℝ)
    (F' : Lp ℂ 2 (Measure.pi fun _ : LayerLink (N / 2) => μG)) :
    ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) ×
      ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → (Fin 7 → G))) → ℂ :=
  fun q => star (⇑F' q.1.1)
    * (blockedLayerKernelPullback μG ρ hN β q * ⇑F' q.2.1)

/-- The pairing integrand of the blocked kernel, at the
(coarse pair) × (fiber pair) grouping. -/
noncomputable def blockedPairingIntegrandSplit (hN : Even N) [NeZero (N / 2)] (β : ℝ)
    (F' : Lp ℂ 2 (Measure.pi fun _ : LayerLink (N / 2) => μG)) :
    ((LayerLink (N / 2) → G) × (LayerLink (N / 2) → G)) ×
      ((LayerLink (N / 2) → (Fin 7 → G)) ×
        (LayerLink (N / 2) → (Fin 7 → G))) → ℂ :=
  fun r => star (⇑F' r.1.1)
    * (blockedLayerKernelIntegrand μG ρ hN β r * ⇑F' r.1.2)

omit [MeasurableInv G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
  [μG.IsMulRightInvariant] [μG.IsInvInvariant] in
/-- The two groupings of the blocked pairing integrand
agree through the middle-exchange regrouping. -/
theorem blockedPairingIntegrandSplit_eq (hN : Even N) [NeZero (N / 2)] (β : ℝ)
    (F' : Lp ℂ 2 (Measure.pi fun _ : LayerLink (N / 2) => μG)) :
    blockedPairingIntegrandSplit μG ρ hN β F'
      = blockedPairingIntegrand μG ρ hN β F'
        ∘ (layerBlockProdComm (G := G) (N := N)).symm := by
  funext r
  show star (⇑F' r.1.1)
      * (blockedLayerKernelIntegrand μG ρ hN β r * ⇑F' r.1.2)
    = star (⇑F' r.1.1)
      * (blockedLayerKernelPullback μG ρ hN β
          ((r.1.1, r.2.1), (r.1.2, r.2.2)) * ⇑F' r.1.2)
  rw [blockedLayerKernelPullback_apply]

/-- The blocked pairing integrand is integrable: it is
dominated by the product of the two coarse `L²` norms of
`F'`, itself integrable by the product rule. -/
theorem blockedPairingIntegrand_integrable (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (F' : Lp ℂ 2 (Measure.pi fun _ : LayerLink (N / 2) => μG)) :
    Integrable (blockedPairingIntegrand μG ρ hN β F')
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) := by
  classical
  have hFn : Integrable (fun U : LayerLink (N / 2) → G => ‖⇑F' U‖)
      (Measure.pi fun _ : LayerLink (N / 2) => μG) :=
    (MeasureTheory.MemLp.integrable one_le_two (MeasureTheory.Lp.memLp F')).norm
  have hA : Integrable
      (fun z : (LayerLink (N / 2) → G)
          × (LayerLink (N / 2) → (Fin 7 → G)) => ‖⇑F' z.1‖)
      ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))) :=
    hFn.comp_fst _
  have hD : Integrable
      (fun q : ((LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G))) ×
          ((LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G))) =>
        ((Real.exp (|β| * layerBoundConst N)
          * (‖⇑F' q.1.1‖ * ‖⇑F' q.2.1‖) : ℝ) : ℂ))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) :=
    ((hA.mul_prod hA).const_mul
      (Real.exp (|β| * layerBoundConst N))).ofReal
  refine Integrable.mono hD ?_ (ae_of_all _ fun q => ?_)
  · have h1 : AEStronglyMeasurable
        (fun q : ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) ×
            ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) => ⇑F' q.1.1)
        (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG))).prod
          ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG)))) :=
      (MeasureTheory.AEStronglyMeasurable.comp_fst
        (MeasureTheory.MemLp.aestronglyMeasurable
          (MeasureTheory.Lp.memLp F'))).comp_fst
    have h2 : AEStronglyMeasurable
        (fun q : ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) ×
            ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) => ⇑F' q.2.1)
        (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG))).prod
          ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG)))) :=
      (MeasureTheory.AEStronglyMeasurable.comp_fst
        (MeasureTheory.MemLp.aestronglyMeasurable
          (MeasureTheory.Lp.memLp F'))).comp_snd
    exact h1.star.mul
      ((blockedLayerKernelPullback_aestronglyMeasurable
        μG ρ hN hρcont β).mul h2)
  · have hK : ‖blockedLayerKernelPullback μG ρ hN β q‖
        ≤ Real.exp (|β| * layerBoundConst N) := by
      exact layerKernel_norm_le μG ρ β _ _
    have hnn : (0 : ℝ) ≤ Real.exp (|β| * layerBoundConst N)
        * (‖⇑F' q.1.1‖ * ‖⇑F' q.2.1‖) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    show ‖star (⇑F' q.1.1)
        * (blockedLayerKernelPullback μG ρ hN β q * ⇑F' q.2.1)‖
      ≤ ‖((Real.exp (|β| * layerBoundConst N)
          * (‖⇑F' q.1.1‖ * ‖⇑F' q.2.1‖) : ℝ) : ℂ)‖
    calc ‖star (⇑F' q.1.1)
          * (blockedLayerKernelPullback μG ρ hN β q * ⇑F' q.2.1)‖
        = ‖⇑F' q.1.1‖
            * (‖blockedLayerKernelPullback μG ρ hN β q‖
              * ‖⇑F' q.2.1‖) := by
          simp
      _ ≤ ‖⇑F' q.1.1‖
            * (Real.exp (|β| * layerBoundConst N) * ‖⇑F' q.2.1‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
            (norm_nonneg _)
      _ = Real.exp (|β| * layerBoundConst N)
            * (‖⇑F' q.1.1‖ * ‖⇑F' q.2.1‖) := by ring
      _ = ‖((Real.exp (|β| * layerBoundConst N)
            * (‖⇑F' q.1.1‖ * ‖⇑F' q.2.1‖) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]

/-- The split grouping of the blocked pairing integrand is
integrable, by transport through the middle-exchange
regrouping. -/
theorem blockedPairingIntegrandSplit_integrable (hN : Even N)
    [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (F' : Lp ℂ 2 (Measure.pi fun _ : LayerLink (N / 2) => μG)) :
    Integrable (blockedPairingIntegrandSplit μG ρ hN β F')
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) := by
  classical
  have hκ : MeasurePreserving
      (layerBlockProdComm (G := G) (N := N))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) :=
    measurePreserving_layerBlockProdComm μG
  have hInt : Integrable (blockedPairingIntegrand μG ρ hN β F')
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))) |>.map
        (layerBlockProdComm (G := G) (N := N)).symm) := by
    rw [hκ.symm.map_eq]
    exact blockedPairingIntegrand_integrable μG ρ hN hρcont β F'
  have hg : AEStronglyMeasurable (blockedPairingIntegrand μG ρ hN β F')
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))) |>.map
        (layerBlockProdComm (G := G) (N := N)).symm) := by
    rw [hκ.symm.map_eq]
    exact (blockedPairingIntegrand_integrable μG ρ hN hρcont β F').aestronglyMeasurable
  rw [blockedPairingIntegrandSplit_eq]
  exact (MeasureTheory.integrable_map_measure
    hg hκ.symm.measurable.aemeasurable).mp hInt

/-- **PROP-0, the pullback-pairing identity.** The blocked
pairing of a coarse observable `F'` against the blocked
kernel equals the fine pairing of the block pullback of
`F'` against the fine layer kernel: the blocked pairing
*is* the fine pairing of the pullback, by change of
variables through the assembly (measure-preserving) and
the middle-exchange regrouping. -/
theorem blockedLayerPairing_eq (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (F' : Lp ℂ 2 (Measure.pi fun _ : LayerLink (N / 2) => μG)) :
    inner ℂ F' (integralKernelOp
        (blockedLayerKernelFun_memLp μG ρ hN hρcont β) F')
      = inner ℂ (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) (measurePreserving_layerBlockMap μG hN) F')
          (integralKernelOp (layerKernelFun_memLp μG ρ hρcont β)
            (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) (measurePreserving_layerBlockMap μG hN) F')) := by
  classical
  set hB : MeasurePreserving (layerBlockMap hN)
      (Measure.pi fun _ : LayerLink N => μG)
      (Measure.pi fun _ : LayerLink (N / 2) => μG) :=
    measurePreserving_layerBlockMap μG hN with hBdef
  set hA : MeasurePreserving
      (fun p : (LayerLink (N / 2) → G)
          × (LayerLink (N / 2) → (Fin 7 → G)) =>
        layerBlockAsm hN p.1 p.2)
      ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)))
      (Measure.pi fun _ : LayerLink N => μG) :=
    measurePreserving_layerBlockAsm μG hN with hAdef
  have hΦ : MeasurePreserving
      (Prod.map
        (fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2)
        (fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) :=
    hA.prod hA
  have hκ : MeasurePreserving
      (layerBlockProdComm (G := G) (N := N))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) :=
    measurePreserving_layerBlockProdComm μG
  have hΦInt : Integrable (blockedPairingIntegrand μG ρ hN β F')
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) :=
    blockedPairingIntegrand_integrable μG ρ hN hρcont β F'
  have hΨInt : Integrable (blockedPairingIntegrandSplit μG ρ hN β F')
      (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
        ((Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) :=
    blockedPairingIntegrandSplit_integrable μG ρ hN hρcont β F'
  -- the pulled-back observable, read through the assembly,
  -- is the coarse observable at the block value
  have hfun : (layerBlockMap hN)
        ∘ (fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2) = Prod.fst := by
    funext z
    exact layerBlockMap_asm hN z.1 z.2
  have hLp : MeasureTheory.Lp.compMeasurePreserving
        (fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2) hA
        (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
      = MeasureTheory.Lp.compMeasurePreserving
          ((layerBlockMap hN) ∘ (fun p : (LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G)) =>
            layerBlockAsm hN p.1 p.2)) (hB.comp hA) F' := by
    exact (DFunLike.congr_fun
      (MeasureTheory.Lp.compMeasurePreserving_comp hB hA) F').symm
  have hfae : (fun z => ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
        ((fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2) z))
      =ᵐ[((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG)))] (fun z => ⇑F' z.1) := by
    have e1 := MeasureTheory.Lp.coeFn_compMeasurePreserving
      (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') hA
    have e2 := MeasureTheory.Lp.coeFn_compMeasurePreserving F' (hB.comp hA)
    rw [hLp] at e1
    exact e1.symm.trans (e2.trans (Filter.Eventually.of_forall
      (fun z => by
        show ⇑F' ((layerBlockMap hN ∘ (fun p : (LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G)) =>
            layerBlockAsm hN p.1 p.2)) z) = ⇑F' z.1
        rw [congrFun hfun z])))
  -- coordinate projections of the a.e. identity
  have hfst : ∀ P : ((LayerLink (N / 2) → G)
        × (LayerLink (N / 2) → (Fin 7 → G))) → Prop,
      (∀ᵐ z ∂((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))), P z)
      → ∀ᵐ q ∂(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG))).prod
          ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG)))), P q.1 := by
    intro P hP
    have h0 : ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))) {z | ¬ P z} = 0 := by
      have hmem := MeasureTheory.mem_ae_iff.mp hP
      rwa [show {z | P z}ᶜ = {z | ¬ P z} from rfl] at hmem
    have hnull : (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) {q | ¬ P q.1} = 0 := by
      have hsub : {q : ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) ×
            ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) | ¬ P q.1}
          ⊆ {z | ¬ P z} ×ˢ Set.univ := by
        intro q hq
        exact ⟨hq, Set.mem_univ _⟩
      refine measure_mono_null hsub ?_
      rw [MeasureTheory.Measure.prod_prod, h0, zero_mul]
    have hmem : ∀ᵐ q ∂(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))), P q.1 :=
      MeasureTheory.mem_ae_iff.mpr hnull
    exact hmem
  have hsnd : ∀ P : ((LayerLink (N / 2) → G)
        × (LayerLink (N / 2) → (Fin 7 → G))) → Prop,
      (∀ᵐ z ∂((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))), P z)
      → ∀ᵐ q ∂(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG))).prod
          ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) =>
              (Measure.pi fun _ : Fin 7 => μG)))), P q.2 := by
    intro P hP
    have h0 : ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
        (Measure.pi fun _ : LayerLink (N / 2) =>
          (Measure.pi fun _ : Fin 7 => μG))) {z | ¬ P z} = 0 := by
      have hmem := MeasureTheory.mem_ae_iff.mp hP
      rwa [show {z | P z}ᶜ = {z | ¬ P z} from rfl] at hmem
    have hnull : (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))) {q | ¬ P q.2} = 0 := by
      have hsub : {q : ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) ×
            ((LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G))) | ¬ P q.2}
          ⊆ Set.univ ×ˢ {z | ¬ P z} := by
        intro q hq
        exact ⟨Set.mem_univ _, hq⟩
      refine measure_mono_null hsub ?_
      rw [MeasureTheory.Measure.prod_prod, h0, mul_zero]
    have hmem : ∀ᵐ q ∂(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG)))), P q.2 :=
      MeasureTheory.mem_ae_iff.mpr hnull
    exact hmem
  have h1 : (fun q => ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
        ((fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2) q.1))
      =ᵐ[(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))]
        (fun q => ⇑F' q.1.1) :=
    hfst (fun z => ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
      ((fun p : (LayerLink (N / 2) → G)
          × (LayerLink (N / 2) → (Fin 7 → G)) =>
        layerBlockAsm hN p.1 p.2) z) = ⇑F' z.1) hfae
  have h2 : (fun q => ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
        ((fun p : (LayerLink (N / 2) → G)
            × (LayerLink (N / 2) → (Fin 7 → G)) =>
          layerBlockAsm hN p.1 p.2) q.2))
      =ᵐ[(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))]
        (fun q => ⇑F' q.2.1) :=
    hsnd (fun z => ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
      ((fun p : (LayerLink (N / 2) → G)
          × (LayerLink (N / 2) → (Fin 7 → G)) =>
        layerBlockAsm hN p.1 p.2) z) = ⇑F' z.1) hfae
  have hprod : (fun q => star (⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
          ((fun p : (LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G)) =>
            layerBlockAsm hN p.1 p.2) q.1))
        * (blockedLayerKernelPullback μG ρ hN β q
          * ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
            ((fun p : (LayerLink (N / 2) → G)
                × (LayerLink (N / 2) → (Fin 7 → G)) =>
              layerBlockAsm hN p.1 p.2) q.2)))
      =ᵐ[(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))).prod
        ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
          (Measure.pi fun _ : LayerLink (N / 2) =>
            (Measure.pi fun _ : Fin 7 => μG))))]
        (blockedPairingIntegrand μG ρ hN β F') := by
    filter_upwards [h1, h2] with q hq1 hq2
    show star (⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
          ((fun p : (LayerLink (N / 2) → G)
              × (LayerLink (N / 2) → (Fin 7 → G)) =>
            layerBlockAsm hN p.1 p.2) q.1))
        * (blockedLayerKernelPullback μG ρ hN β q
          * ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
            ((fun p : (LayerLink (N / 2) → G)
                × (LayerLink (N / 2) → (Fin 7 → G)) =>
              layerBlockAsm hN p.1 p.2) q.2))
      = star (⇑F' q.1.1)
        * (blockedLayerKernelPullback μG ρ hN β q * ⇑F' q.2.1)
    rw [hq1, hq2]
  calc inner ℂ F' (integralKernelOp
          (blockedLayerKernelFun_memLp μG ρ hN hρcont β) F')
      = ∫ p, star (⇑F' p.1)
            * (blockedLayerKernelFun μG ρ hN β p * ⇑F' p.2)
          ∂((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
            (Measure.pi fun _ : LayerLink (N / 2) => μG)) :=
        integralKernelOp_inner _ _ _
    _ = ∫ r, blockedPairingIntegrandSplit μG ρ hN β F' r
          ∂(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
              (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
            ((Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)).prod
              (Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)))) := by
        rw [MeasureTheory.integral_prod _ hΨInt]
        refine MeasureTheory.integral_congr_ae
          (ae_of_all _ fun p => ?_)
        show star (⇑F' p.1)
            * ((∫ q, blockedLayerKernelIntegrand μG ρ hN β (p, q)
                ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                    (Measure.pi fun _ : Fin 7 => μG)).prod
                  (Measure.pi fun _ : LayerLink (N / 2) =>
                    (Measure.pi fun _ : Fin 7 => μG)))) * ⇑F' p.2)
          = ∫ q, blockedPairingIntegrandSplit μG ρ hN β F' (p, q)
              ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)).prod
                (Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)))
        symm
        calc ∫ q, blockedPairingIntegrandSplit μG ρ hN β F' (p, q)
              ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)).prod
                (Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)))
            = ∫ q, star (⇑F' p.1)
                * (blockedLayerKernelIntegrand μG ρ hN β (p, q)
                  * ⇑F' p.2) ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)).prod
                (Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG))) := rfl
          _ = ∫ q, (star (⇑F' p.1)
                * blockedLayerKernelIntegrand μG ρ hN β (p, q))
                * ⇑F' p.2 ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)).prod
                (Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG))) :=
              MeasureTheory.integral_congr_ae
                (ae_of_all _ fun q => (mul_assoc _ _ _).symm)
          _ = star (⇑F' p.1)
                * ((∫ q, blockedLayerKernelIntegrand μG ρ hN β (p, q)
                    ∂((Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)).prod
                (Measure.pi fun _ : LayerLink (N / 2) =>
                  (Measure.pi fun _ : Fin 7 => μG)))) * ⇑F' p.2) := by
              rw [MeasureTheory.integral_mul_const,
                MeasureTheory.integral_const_mul, mul_assoc]
    _ = ∫ q, blockedPairingIntegrand μG ρ hN β F' q
          ∂(((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
              (Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG))).prod
            ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
              (Measure.pi fun _ : LayerLink (N / 2) =>
                (Measure.pi fun _ : Fin 7 => μG)))) := by
        rw [blockedPairingIntegrandSplit_eq, ← hκ.symm.map_eq]
        have hΦInt' : Integrable (blockedPairingIntegrand μG ρ hN β F')
            (Measure.map ⇑(layerBlockProdComm (G := G) (N := N)).symm
              (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
                  (Measure.pi fun _ : LayerLink (N / 2) => μG)).prod
                ((Measure.pi fun _ : LayerLink (N / 2) =>
                    (Measure.pi fun _ : Fin 7 => μG)).prod
                  (Measure.pi fun _ : LayerLink (N / 2) =>
                    (Measure.pi fun _ : Fin 7 => μG))))) := by
          rwa [hκ.symm.map_eq]
        exact (MeasureTheory.integral_map hκ.symm.measurable.aemeasurable
          hΦInt'.aestronglyMeasurable).symm
    _ = ∫ p, star (⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') p.1)
            * (layerKernelFun μG ρ β p
              * ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') p.2)
          ∂((Measure.pi fun _ : LayerLink N => μG).prod
            (Measure.pi fun _ : LayerLink N => μG)) := by
        have hfine : Integrable
            (fun p : (LayerLink N → G) × (LayerLink N → G) =>
              star (⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') p.1)
                * (layerKernelFun μG ρ β p
                  * ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') p.2))
            ((Measure.pi fun _ : LayerLink N => μG).prod
              (Measure.pi fun _ : LayerLink N => μG)) :=
          integrable_kernel_pairing_gen
            (layerKernelFun_memLp μG ρ hρcont β) _ _
        have hfine' : Integrable
            (fun p : (LayerLink N → G) × (LayerLink N → G) =>
              star (⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') p.1)
                * (layerKernelFun μG ρ β p
                  * ⇑(MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F') p.2))
            (Measure.map (Prod.map
                (fun p : (LayerLink (N / 2) → G)
                    × (LayerLink (N / 2) → (Fin 7 → G)) =>
                  layerBlockAsm hN p.1 p.2)
                (fun p : (LayerLink (N / 2) → G)
                    × (LayerLink (N / 2) → (Fin 7 → G)) =>
                  layerBlockAsm hN p.1 p.2))
              (((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
                  (Measure.pi fun _ : LayerLink (N / 2) =>
                    (Measure.pi fun _ : Fin 7 => μG))).prod
                ((Measure.pi fun _ : LayerLink (N / 2) => μG).prod
                  (Measure.pi fun _ : LayerLink (N / 2) =>
                    (Measure.pi fun _ : Fin 7 => μG))))) := by
          rwa [hΦ.map_eq]
        have htr := MeasureTheory.integral_map hΦ.measurable.aemeasurable
          hfine'.aestronglyMeasurable
        rw [hΦ.map_eq] at htr
        exact (MeasureTheory.integral_congr_ae hprod.symm).trans htr.symm
    _ = inner ℂ (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')
          (integralKernelOp (layerKernelFun_memLp μG ρ hρcont β)
            (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) hB F')) :=
        (integralKernelOp_inner _ _ _).symm

/-- **PROP-1A (one-step positivity propagation,
conditional).** GIVEN the all-of-`L²` positivity of the
fine layer kernel (`LayerKernelPosAll`, the hypothesis
named on the face — not discharged here), the blocked
layer kernel is positive at the `PosKernel` level: its
pairing against any coarse observable equals, by
`blockedLayerPairing_eq`, the fine pairing of the block
pullback. This is the trivial (pullback) direction of
propagation, landed as infrastructure: it says positivity
transports across one blocking step for every
`PosKernel`-level statement, and nothing about the
gauge-invariant class (`LayerKernelPos`), the margin, or
iteration. -/
theorem blockedLayerKernelFun_posKernel_of_layerKernelPosAll
    (hN : Even N) [NeZero (N / 2)]
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (hAll : LayerKernelPosAll (N := N) μG ρ hρcont β) :
    PosKernel (blockedLayerKernelFun μG ρ hN β)
      (blockedLayerKernelFun_memLp μG ρ hN hρcont β) := by
  intro F'
  have h := hAll (MeasureTheory.Lp.compMeasurePreserving (layerBlockMap hN) (measurePreserving_layerBlockMap μG hN) F')
  rw [blockedLayerPairing_eq μG ρ hN hρcont β F']
  exact h

end Pairing

end ThetLogos

