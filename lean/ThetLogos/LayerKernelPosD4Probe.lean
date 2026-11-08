/-
# R2 — the D₄ miniature probe: `LayerKernelPos` at (D₄, std)

**R2** (priced S, 2026-11-05; enrolled by Jeff's "build all you
can", 2026-11-07).  The question: `LayerKernelPos` — the
registered 𝒜 ⪰ 0 target of Brick A0 (`LayerKernelPos.lean`) — at
the smallest seat the landed supports do not reach: the dihedral
group `D₄` of order 8 with its two-dimensional standard
representation, at layer extent `N = 2`, for all `β ≥ 0`.

Standing when this probe opens (all T1, verified against the
tree):

* `LayerKernelPos` is proved at `β = 0` in general, at the
  binary seat, at the abelian family (R1), at the ternary seat
  for all `β ≥ 0` (TM-3), and for every finite `G` with every
  **one-dimensional** unitary representation at even `N`, all
  `β ≥ 0` (G-1's landed sector, `LayerKernelGramCertOneDim`).
* The Gram/SOS certificate infrastructure (G-0,
  `LayerKernelGramCert`) and the retrofit instances (G-0b) are
  in the tree: a `LayerKernelSOSCert` discharges
  `LayerKernelPos` once, at the pin's generality.
* The D₄ seat data already exists in the tree for the RG-2c
  seat (`BlockingProjectionNonab`): `DihedralGroup 4`, the
  uniform probability measure `nbμG`, and the faithful
  two-dimensional unitary representation `nbRep` with
  `nbRot = !![0, -1; 1, 0]` and `nbRefl = !![1, 0; 0, -1]` —
  exactly the scoping's `ρ(r)`, `ρ(s)`
  (`gram-sos-lkp-scoping-2026-11-05.md` §3.1).
* The 2026-11-05 numeric probe at this seat (three engines,
  exact rational arithmetic on the third) found: the column
  expansion's five coefficients are all `≥ 0` in closed form
  (Q1); no PSD obstruction on a 42-configuration sample at the
  landmark couplings (Q2); sector-wise assembly surviving at
  probe rank with the two-dimensional sector dominant at
  `β ≥ 0.7` (Q3).  That is T2 evidence about the certificate
  route, fenced as such in the scoping (§3.2): it neither
  proves nor refutes the instance pinned below.

The instance statement is `layerKernelPosD4Std` (§1): THE
landed `LayerKernelPos` predicate at `μG = nbμG`,
`ρ = nbRep`, `N = 2` — not a paraphrase.

**Probe outcome: PRICED OBSTRUCTION.**  The instance is
pinned and elaborated, and the certificate route is landed
at this seat except for exactly one named field.  Landed in
this module, all at T1 on the standard axiom set
(`propext`, `Classical.choice`, `Quot.sound` — audited at
the foot of §6):

* the pin (§1);
* **Q1 in Lean** (§§2–4): the five irreducible types of
  `D₄` as data, the column expansion `d4_expansion` — the
  `expansion` field of a seat certificate — and coefficient
  nonnegativity `d4Coeff_nonneg`.  The 2026-11-05 probe's
  exact coefficient computation is thereby kernel-checked:
  **K-GRAM-SECTOR does not fire** (no negative coefficient
  exists at this seat);
* the seat's sum forms (§5): the kernel as the finite
  stratum average, and the pairing as the finite double
  sum with its nonnegative scalar — the certificate's
  `pairing_eq` field, discharged;
* the reduction (§6): `layerKernelPos_of_d4KernelEqGap` —
  the pinned instance follows from the single remaining
  proposition `d4KernelEqGap`, the certificate's
  `kernel_eq` field for the landed expansion data,
  assembled through G-0's discharge.  The remainder is one
  named statement, not a fog.

**The missing infrastructure, named exactly:** the
separation identities for types of dimension `≥ 2`.  For a
multi-index whose column types include `std`, the stratum
average of the product of column characters must be
reassembled as a sum of separated squares
`Σ_k Φ_k(u) · conj(Φ_k(u'))`.  For one-dimensional types
this is the character filter, the mechanism of every landed
support (binary seat, abelian family, ternary seat, and
G-1's one-dimensional sector — whose `gram_kernel_eq` is
the `d = 1` form of exactly this step).  For `std` the
per-site average is a tensor contraction: the projection
of tensor powers of `ρ` onto their intertwiner channels
(Weingarten-type data; e.g. `std ⊗ std` decomposes over
the four one-dimensional types of `D₄`).  Neither the
pinned Mathlib (finite-group character theory stops at
character orthogonality) nor the tree formalizes it.  This
is the higher-dimensional sector of G-1, named open on the
face of `LayerKernelGramCertOneDim`; its first seat is
this one.

**Kills:** **K-LKP-MINI-D4 does not fire** — the instance
is not refuted; no negative is proved or claimed anywhere
in this probe, and the certificate evidence points the
other way (nonnegative expansion at T1; the 2026-11-05
sample-PSD shadow clean).  **K-GRAM-DEGEN does not fire**
— no certificate is constructed here, degenerate or
otherwise.  The instance stands OPEN, reduced at T1 to
`d4KernelEqGap`.

**Priced remainder:** the `std` separation identities at
this single seat (explicit intertwiner features for `D₄`
plus the column-graph contraction at `N = 2`, then §6's
assembly discharges it) — band **M**; the general
finite-group `d ≥ 2` sector of G-1 (a finite-group
contraction API, then the same assembly uniformly in
`(G, ρ)`) — band **L (M–L)**, the G-1 remainder of the
Gram/SOS menu.

NO CLAIM; parts of the Clay statement closed: 0; dials 0/4;
Dial 3 = 0 whatever this probe returns (one instance does not
close Band B).

**Integration repair (2026-11-08, at integration):** the
first integration attempt stopped at the axiom-fence step:
the fence's co-import of this module failed — "environment
already contains 'ThetLogos.instDecidableEqLayerLinkOfNatNat'
from ThetLogos.LayerKernelPosSeatProbe" — because the
anonymous classical `DecidableEq (LayerLink 2)` instance
below and the seat probe's anonymous classical instance
for the same type receive the same compiler-generated
name. The repair, at integration and in the minimal class
of the UA-3 / AB-7 precedents: the instance below carries
the explicit name `d4InstDecidableEqLayerLink`. Its
definition is byte-identical to the lane's anonymous
instance (`fun a b => Classical.propDecidable _`), no
statement in this module changes, and no other module is
touched. The fence was then re-run from the top; its
verdict is on this shipment's ledger record.
-/

import ThetLogos.LayerKernelPos
import ThetLogos.LayerKernelGramCert
import ThetLogos.LayerKernelGramCertOneDim
import ThetLogos.BlockingProjectionNonab

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

/-! ## §1. The pin

`LayerKernelPos` at the D₄ miniature: for every `β ≥ 0`, the
one-layer kernel at `(DihedralGroup 4, nbμG, nbRep)`, extent
`N = 2` (8 layer sites, 24 columns), is nonnegative on
gauge-invariant layer observables.  This is G-1's D₄ instance —
the first seat of the higher-dimensional sector named open on
the face of `LayerKernelGramCertOneDim`. -/

/-- **R2's question, pinned**: `LayerKernelPos` at
`(G, μG, ρ, N) = (DihedralGroup 4, nbμG, nbRep, 2)`, for all
`β ≥ 0`.  Statement only; nothing in this section asserts it. -/
def layerKernelPosD4Std : Prop :=
  ∀ β : ℝ, 0 ≤ β → LayerKernelPos (N := 2) nbμG nbRep β

/-! ## §2. The column expansion at the seat (Q1, in Lean)

The certificate route's first half is the column expansion of
the scoping's §2 pin: the one-column Boltzmann factor
`exp(−β·dens_ρ g)` written as a nonnegative combination of the
characters of `G`.  At `D₄` there are five irreducible types —
the trivial representation, the three sign representations
`τ_{ε,δ}` (`r ↦ ε`, `s ↦ δ`), and the two-dimensional standard
representation — and the 2026-11-05 probe computed the
expansion exactly (its Q1): with `t = e^{−β}`,

* `c_triv = (1 + 6t + t²)/8`,
* `c_{τ} = (1 − t)²/8` for each of the three sign types,
* `c_std = (1 − t²)/4`,

all `≥ 0` for `β ≥ 0`.  This section lands that computation at
T1: the types and characters as Lean data (`D4Type`, `d4Char`),
the coefficients (`d4Coeff`), their nonnegativity
(`d4Coeff_nonneg`), and the expansion identity itself
(`d4_expansion`, §4, after the character table of `nbRep`). -/

/-- The five irreducible types of `D₄`: trivial, the three
sign representations, and the two-dimensional standard
representation. -/
inductive D4Type | triv | sgnA | sgnB | sgnC | std
  deriving DecidableEq

/-- The five types as a `Fintype` (manual instance: the
`deriving Fintype` handler's generated completeness proof
fails on this inductive in the pinned toolchain — its
`enumList` nodup coercion does not elaborate; recorded here
so the manual instance is not mistaken for a shortcut). -/
instance : Fintype D4Type where
  elems := {.triv, .sgnA, .sgnB, .sgnC, .std}
  complete := by
    intro x
    cases x <;> simp

/-- A sign character of `D₄`: `r i ↦ ε^(i.val)`,
`sr i ↦ δ · ε^(i.val)`, for `ε, δ ∈ {1, −1}`. -/
def d4SignChar (ε δ : ℂ) : DihedralGroup 4 → ℂ
  | .r i => ε ^ i.val
  | .sr i => δ * ε ^ i.val

/-- The character of a `D4Type`: `sgnA = τ_{−1, 1}`,
`sgnB = τ_{1, −1}`, `sgnC = τ_{−1, −1}`, and `std` is the
trace of the seat representation `nbRep`. -/
noncomputable def d4Char : D4Type → DihedralGroup 4 → ℂ
  | .triv => fun _ => 1
  | .sgnA => d4SignChar (-1) 1
  | .sgnB => d4SignChar 1 (-1)
  | .sgnC => d4SignChar (-1) (-1)
  | .std => fun g => charFn nbRep g

/-- The column-expansion coefficients at the D₄ seat, as
functions of `β` (through `t = e^{−β}`): the exact values of
the 2026-11-05 probe's Q1. -/
noncomputable def d4Coeff (β : ℝ) : D4Type → ℝ
  | .triv => (1 + 6 * Real.exp (-β) + (Real.exp (-β)) ^ 2) / 8
  | .sgnA => (1 - Real.exp (-β)) ^ 2 / 8
  | .sgnB => (1 - Real.exp (-β)) ^ 2 / 8
  | .sgnC => (1 - Real.exp (-β)) ^ 2 / 8
  | .std => (1 - (Real.exp (-β)) ^ 2) / 4

/-- Sums over the five types, unfolded. -/
theorem sum_D4Type {X : Type*} [AddCommMonoid X] (F : D4Type → X) :
    ∑ τ, F τ = F .triv + F .sgnA + F .sgnB + F .sgnC + F .std := by
  have h : (Finset.univ : Finset D4Type)
      = {.triv, .sgnA, .sgnB, .sgnC, .std} := rfl
  rw [h]
  simp only [Finset.sum_insert (by decide : D4Type.triv
      ∉ ({.sgnA, .sgnB, .sgnC, .std} : Finset D4Type)),
    Finset.sum_insert (by decide : D4Type.sgnA
      ∉ ({.sgnB, .sgnC, .std} : Finset D4Type)),
    Finset.sum_insert (by decide : D4Type.sgnB
      ∉ ({.sgnC, .std} : Finset D4Type)),
    Finset.sum_insert (by decide : D4Type.sgnC
      ∉ ({.std} : Finset D4Type)),
    Finset.sum_singleton]
  simp only [← add_assoc]

/-- **Q1, the sign half, at T1**: every column-expansion
coefficient at the D₄ seat is nonnegative for `β ≥ 0` (the
sign coefficients are squares; `c_std = (1−t)(1+t)/4` with
`t = e^{−β} ∈ (0, 1]`).  In particular **K-GRAM-SECTOR's
coefficient clause does not fire at this seat**. -/
theorem d4Coeff_nonneg {β : ℝ} (hβ : 0 ≤ β) (τ : D4Type) :
    0 ≤ d4Coeff β τ := by
  have ht0 : 0 < Real.exp (-β) := Real.exp_pos _
  have ht1 : Real.exp (-β) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show (-β : ℝ) ≤ 0 by linarith)
    rwa [Real.exp_zero] at h
  cases τ <;> simp only [d4Coeff]
  · positivity
  · positivity
  · positivity
  · positivity
  · have h : (1 : ℝ) - (Real.exp (-β)) ^ 2
        = (1 - Real.exp (-β)) * (1 + Real.exp (-β)) := by ring
    rw [h]
    exact div_nonneg
      (mul_nonneg (by linarith) (by linarith)) (by norm_num)

/-! ## §3. The character table of `nbRep` and the density table

The standard character of `D₄`: `χ = (2, −2, 0, 0, 0)` on the
classes `({1}, {r²}, {r, r³}, {s, r²s}, {rs, r³s})` — here
proved element-wise from the tree's matrices.  The density
`gramDens nbRep g = 1 − χ(g)/2` therefore takes the values
`0` at `1`, `2` at `r²`, and `1` at the other six elements. -/

theorem charFn_nbRep_r_zero : charFn nbRep (.r 0) = 2 := by
  show Matrix.trace (nbRepMat (.r 0)) = 2
  rw [show nbRepMat (.r 0) = (1 : Matrix (Fin 2) (Fin 2) ℂ) from
    nbRotZ_zero]
  simp

theorem charFn_nbRep_r_one : charFn nbRep (.r 1) = 0 := by
  show Matrix.trace (nbRepMat (.r 1)) = 0
  rw [show nbRepMat (.r 1) = nbRot from by
    rw [show nbRepMat (.r 1) = nbRotZ 1 from rfl, nbRotZ,
      show (1 : ZMod 4).val = 1 from rfl, pow_one]]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, nbRot]

theorem charFn_nbRep_r_two : charFn nbRep (.r 2) = -2 := by
  show Matrix.trace (nbRepMat (.r 2)) = -2
  rw [show nbRepMat (.r 2) = (-1 : Matrix (Fin 2) (Fin 2) ℂ) from by
    rw [show nbRepMat (.r 2) = nbRotZ 2 from rfl, nbRotZ,
      show (2 : ZMod 4).val = 2 from rfl]
    exact nbRot_sq]
  simp

theorem charFn_nbRep_r_three : charFn nbRep (.r 3) = 0 := by
  show Matrix.trace (nbRepMat (.r 3)) = 0
  rw [show nbRepMat (.r 3) = -nbRot from by
    rw [show nbRepMat (.r 3) = nbRotZ 3 from rfl, nbRotZ,
      show (3 : ZMod 4).val = 3 from rfl, pow_succ, nbRot_sq]
    simp [pow_succ, nbRot_sq]]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, nbRot]

theorem nbRotZ_zero_mul_nbRefl :
    nbRotZ 0 * nbRefl = !![1, 0; 0, -1] := by
  rw [nbRotZ_zero, Matrix.one_mul]
  rfl

theorem nbRotZ_one_mul_nbRefl :
    nbRotZ 1 * nbRefl = !![0, 1; 1, 0] := by
  rw [nbRotZ, show (1 : ZMod 4).val = 1 from rfl, pow_one]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [nbRot, nbRefl, Matrix.mul_apply, Fin.sum_univ_two]

theorem nbRotZ_two_mul_nbRefl :
    nbRotZ 2 * nbRefl = !![-1, 0; 0, 1] := by
  rw [nbRotZ, show (2 : ZMod 4).val = 2 from rfl, nbRot_sq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [nbRefl, Matrix.mul_apply, Fin.sum_univ_two]

theorem nbRotZ_three_mul_nbRefl :
    nbRotZ 3 * nbRefl = !![0, -1; -1, 0] := by
  rw [nbRotZ, show (3 : ZMod 4).val = 3 from rfl, pow_succ, nbRot_sq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [nbRot, nbRefl, Matrix.mul_apply, Fin.sum_univ_two]

theorem charFn_nbRep_sr (i : ZMod 4) : charFn nbRep (.sr i) = 0 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have h : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      decide
    exact h i
  show Matrix.trace (nbRepMat (.sr i)) = 0
  rcases hi with rfl | rfl | rfl | rfl
  · rw [show nbRepMat (.sr 0) = nbRotZ 0 * nbRefl from rfl,
      nbRotZ_zero_mul_nbRefl]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · rw [show nbRepMat (.sr 1) = nbRotZ (-1) * nbRefl from rfl,
      show (-(1 : ZMod 4)) = 3 by decide, nbRotZ_three_mul_nbRefl]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · rw [show nbRepMat (.sr 2) = nbRotZ (-2) * nbRefl from rfl,
      show (-(2 : ZMod 4)) = 2 by decide, nbRotZ_two_mul_nbRefl]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · rw [show nbRepMat (.sr 3) = nbRotZ (-3) * nbRefl from rfl,
      show (-(3 : ZMod 4)) = 1 by decide, nbRotZ_one_mul_nbRefl]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- The density at the identity is `0`. -/
theorem gramDens_nbRep_r_zero : gramDens nbRep (.r 0) = 0 := by
  rw [gramDens, charFn_nbRep_r_zero]
  norm_num

/-- The density at `r²` is `2`. -/
theorem gramDens_nbRep_r_two : gramDens nbRep (.r 2) = 2 := by
  rw [gramDens, charFn_nbRep_r_two]
  norm_num

/-- The density at every other element is `1`. -/
theorem gramDens_nbRep_of_ne (g : DihedralGroup 4)
    (h0 : g ≠ .r 0) (h2 : g ≠ .r 2) : gramDens nbRep g = 1 := by
  have hc : charFn nbRep g = 0 := by
    cases g with
    | r i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        have h : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
          decide
        exact h i
      rcases hi with rfl | rfl | rfl | rfl
      · exact absurd rfl h0
      · exact charFn_nbRep_r_one
      · exact absurd rfl h2
      · exact charFn_nbRep_r_three
    | sr i => exact charFn_nbRep_sr i
  rw [gramDens, hc]
  norm_num

/-! ## §4. The column expansion identity (Q1, completed at T1)

The one-column Boltzmann factor at the seat is the
nonnegative character combination of §2, for every group
element: this is exactly the `expansion` field a
`LayerKernelSOSCert` at this seat would carry.  The proof is
by the eight elements: the density table (§3) reduces the
left side to `1`, `t`, or `t²` (with `t = e^{−β}`), the
character table reduces the right side to a polynomial in
`t`, and the two agree — the reflection cases uniformly,
because the two sign coefficients that see `r`'s parity
carry the same weight and cancel. -/

/-- **Q1 at T1 — the column expansion at the D₄ seat.**
For every `β` and every `g : D₄`,
`exp(−β · dens_std(g)) = Σ_τ c_τ(β) · χ_τ(g)` with the
coefficients of `d4Coeff` (nonnegative for `β ≥ 0`, by
`d4Coeff_nonneg`). -/
theorem d4_expansion (β : ℝ) (g : DihedralGroup 4) :
    ((Real.exp (-β * gramDens nbRep g) : ℝ) : ℂ)
      = ∑ τ, ((d4Coeff β τ : ℝ) : ℂ) * d4Char τ g := by
  have hexp2 : Real.exp (-β * 2) = (Real.exp (-β)) ^ 2 := by
    rw [show (-β * 2 : ℝ) = (-β) + (-β) by ring, Real.exp_add,
      ← pow_two]
  have hv1 : (1 : ZMod 4).val = 1 := rfl
  have hv2 : (2 : ZMod 4).val = 2 := rfl
  have hv3 : (3 : ZMod 4).val = 3 := rfl
  rw [sum_D4Type]
  cases g with
  | r i =>
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      have h : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
        decide
      exact h i
    rcases hi with rfl | rfl | rfl | rfl
    · rw [gramDens_nbRep_r_zero]
      simp only [d4Char, d4SignChar, d4Coeff, charFn_nbRep_r_zero,
        ZMod.val_zero, pow_zero, mul_zero, Real.exp_zero]
      push_cast
      ring
    · rw [gramDens_nbRep_of_ne _ (by decide) (by decide)]
      simp only [d4Char, d4SignChar, d4Coeff, charFn_nbRep_r_one,
        hv1, pow_one, mul_one]
      push_cast
      ring
    · rw [gramDens_nbRep_r_two, hexp2]
      simp only [d4Char, d4SignChar, d4Coeff, charFn_nbRep_r_two,
        hv2]
      push_cast
      ring
    · rw [gramDens_nbRep_of_ne _ (by decide) (by decide)]
      simp only [d4Char, d4SignChar, d4Coeff, charFn_nbRep_r_three,
        hv3, mul_one]
      push_cast
      ring
  | sr i =>
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      have h : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
        decide
      exact h i
    have hd : gramDens nbRep (.sr i) = 1 :=
      gramDens_nbRep_of_ne _ (by intro h; cases h)
        (by intro h; cases h)
    rw [hd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [d4Char, d4SignChar, d4Coeff, charFn_nbRep_sr,
        ZMod.val_zero, hv1, hv2, hv3, pow_zero, pow_one, mul_one] <;>
      push_cast <;> ring

/-! ## §5. The seat's sum forms

At a finite seat the kernel and the `LayerKernelPos`
pairing are finite sums: the stratum integral is the uniform
average over the `8^8` stratum configurations, and the
pairing integral is the uniform average over configuration
pairs.  These are the regime evaluations any certificate
assembly at this seat consumes — the second is exactly the
`pairing_eq` field of `LayerKernelSOSCert`, discharged here
with `pairScale = (8^{24})^{−2}` (kept symbolic as the
configuration count).  Both go through the finite-Haar
evaluations landed with G-1's one-dimensional sector
(`integral_pi_eq_card_inv_sum`). -/

/-- Decidable equality on layer links at the seat (the
side condition G-0's certificate and G-1's headline carry
as a hypothesis; discharged here classically, once, for
this seat's configuration type). The instance carries an
explicit name: the anonymous form's compiler-generated
name is the same one `LayerKernelPosSeatProbe`'s classical
instance for this type generates, and the two collide
under co-import — see the integration repair note in the
module header. The definition is unchanged. -/
noncomputable instance d4InstDecidableEqLayerLink :
    DecidableEq (LayerLink 2) :=
  fun a b => Classical.propDecidable _

/-- The kernel at the seat is the finite stratum average. -/
theorem layerKernel_d4_eq_sum (β : ℝ)
    (u u' : LayerLink 2 → DihedralGroup 4) :
    layerKernel nbμG nbRep β u u'
      = ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ)⁻¹)
          • ∑ α, (Real.exp (-(layerAction nbRep β α u u')) : ℂ) := by
  show (∫ α : LayerSite 2 → DihedralGroup 4,
      (Real.exp (-(layerAction nbRep β α u u')) : ℂ)
      ∂(Measure.pi fun _ : LayerSite 2 => nbμG)) = _
  exact integral_pi_eq_card_inv_sum nbμG
    (fun α => (Real.exp (-(layerAction nbRep β α u u')) : ℂ))

/-- The pairing at the seat is the finite double sum, with
the nonnegative scalar `(card (LayerLink 2 → D₄))^{−2}` —
the `pairing_eq` field of a seat certificate, discharged. -/
theorem pairing_d4_eq (β : ℝ)
    (F : (LayerLink 2 → DihedralGroup 4) → ℂ) :
    (∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * layerKernel nbμG nbRep β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink 2 => nbμG)
        ∂(Measure.pi fun _ : LayerLink 2 => nbμG))
      = (((Fintype.card (LayerLink 2 → DihedralGroup 4) : ℝ)⁻¹
            ^ 2 : ℝ) : ℂ)
          * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
              * layerKernel nbμG nbRep β u u' * F u' := by
  set c : ℝ := (Fintype.card (LayerLink 2 → DihedralGroup 4) : ℝ)⁻¹
  calc (∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * layerKernel nbμG nbRep β u u' * F u'
          ∂(Measure.pi fun _ : LayerLink 2 => nbμG)
        ∂(Measure.pi fun _ : LayerLink 2 => nbμG))
      = ∫ u, (c • ∑ u', (starRingEnd ℂ) (F u)
          * layerKernel nbμG nbRep β u u' * F u')
          ∂(Measure.pi fun _ : LayerLink 2 => nbμG) := by
        refine integral_congr_ae (Filter.Eventually.of_forall
          fun u => ?_)
        exact integral_pi_eq_card_inv_sum nbμG
          (fun u' => (starRingEnd ℂ) (F u)
            * layerKernel nbμG nbRep β u u' * F u')
    _ = c • ∫ u, (∑ u', (starRingEnd ℂ) (F u)
          * layerKernel nbμG nbRep β u u' * F u')
          ∂(Measure.pi fun _ : LayerLink 2 => nbμG) :=
        integral_smul c _
    _ = c • (c • ∑ u, ∑ u', (starRingEnd ℂ) (F u)
          * layerKernel nbμG nbRep β u u' * F u') := by
        rw [integral_pi_eq_card_inv_sum]
    _ = (((c ^ 2 : ℝ)) : ℂ)
          * ∑ u, ∑ u', (starRingEnd ℂ) (F u)
              * layerKernel nbμG nbRep β u u' * F u' := by
        rw [smul_smul, Complex.real_smul]
        congr 1
        rw [pow_two]

/-! ## §6. The verdict: reduction to the separation gap

What remains is exactly one field of the certificate: the
assembled kernel identity (`kernel_eq`), i.e. the separation
identities (PIN-F) for the multi-indices of §2.  The
definition below names that remainder in the corpus's own
vocabulary — the kernel written as a Gram sum over some
finite joint index set, with the assembled weights of the
LANDED expansion (§2/§4) — and the theorem after it proves
that the gap so named is the *whole* remainder: given it,
the certificate assembles from this module's landed fields
and G-0's discharge closes the pinned instance. -/

/-- **The separation gap at the seat, named**: some finite
joint index set, type readout, and feature family assemble
the kernel as a Gram sum with the weights of the landed
column expansion.  This is the one certificate field this
probe does not supply.  It is a statement, not an assertion:
nothing in this module claims it holds. -/
def d4KernelEqGap (β : ℝ) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι)
    (τof : ι → LayerColumn 2 → D4Type)
    (feat : ι → (LayerLink 2 → DihedralGroup 4) → ℂ),
    ∀ u u' : LayerLink 2 → DihedralGroup 4,
      layerKernel nbμG nbRep β u u'
        = ∑ j, ((gramColWeight (d4Coeff β) τof j : ℝ) : ℂ)
            * feat j u * star (feat j u')

/-- **The reduction (T1)**: the pinned instance follows from
the separation gap alone — every other field of the seat
certificate is landed in this module (`d4Coeff_nonneg`,
`d4_expansion`, `pairing_d4_eq`), and G-0's discharge
(`LayerKernelSOSCert.layerKernelPos`) does the rest. -/
theorem layerKernelPos_of_d4KernelEqGap {β : ℝ} (hβ : 0 ≤ β)
    (h : d4KernelEqGap β) :
    LayerKernelPos (N := 2) nbμG nbRep β := by
  obtain ⟨ι, hι, τof, feat, hkernel⟩ := h
  haveI := hι
  -- The gap's `Fintype ι` and the ambient one are equal
  -- (`Fintype` is a subsingleton); transport the kernel
  -- equation across that equality of index finsets.
  have huniv : @Finset.univ ι hι = Finset.univ :=
    congrArg (fun I : Fintype ι => @Finset.univ ι I)
      (Subsingleton.elim hι _)
  have hkernel' : ∀ u u' : LayerLink 2 → DihedralGroup 4,
      layerKernel nbμG nbRep β u u'
        = ∑ j, ((gramColWeight (d4Coeff β) τof j : ℝ) : ℂ)
            * feat j u * star (feat j u') := by
    intro u u'
    have h2 := hkernel u u'
    rw [huniv] at h2
    exact h2
  let cert : LayerKernelSOSCert (N := 2) (τ := D4Type)
      (ι := ι) nbμG nbRep β :=
    { coeff := d4Coeff β
      coeff_nonneg := d4Coeff_nonneg hβ
      char := d4Char
      expansion := d4_expansion β
      τof := τof
      feat := feat
      pairScale :=
        (Fintype.card (LayerLink 2 → DihedralGroup 4) : ℝ)⁻¹ ^ 2
      pairScale_nonneg := by
        rw [pow_two]; exact mul_self_nonneg _
      pairing_eq := pairing_d4_eq β
      kernel_eq := hkernel' }
  exact cert.layerKernelPos

/-- The pinned statement `layerKernelPosD4Std`, reduced to
the gap at every `β ≥ 0`. -/
theorem layerKernelPosD4Std_of_gaps
    (h : ∀ β : ℝ, 0 ≤ β → d4KernelEqGap β) :
    layerKernelPosD4Std :=
  fun β hβ => layerKernelPos_of_d4KernelEqGap hβ (h β hβ)

-- Axiom audit for this module's headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms d4_expansion
#print axioms d4Coeff_nonneg
#print axioms layerKernel_d4_eq_sum
#print axioms pairing_d4_eq
#print axioms layerKernelPos_of_d4KernelEqGap

end ThetLogos
