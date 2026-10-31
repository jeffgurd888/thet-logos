import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.SpecialFunctions.Exp
import ThetLogos.Q7C4R4Assembly
import ThetLogos.Q7C4R4Spectrum
import ThetLogos.Q7C4R4Charge
import ThetLogos.SpectralActionQ7CR

/-!
# ThetLogos.Q7C4R4Dynamics — dynamics as an owned object for the
Q⁷C⁴R⁴ composite (Q7CR-5)

**Status: T1 certification brick at a named, labeled choice.
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing pack: `pack-q7cr-5.md` (gauntlet item 6, dynamics; no
kill is armed on this brick). Gates LANDED: Q7CR-1b (composite
Dirac + D² identity), Q7CR-2 (`Q7C4R4Spectrum`: the instantiated
seat — eigenbasis `basisComp`, eigenvalue function `eigComp`, all
eigenvalues in `[1/64, 841/64]`, multiset `spectrumQ7CR2`), SA2
(`SpectralActionQ7CR`: spectral lists, heat-trace factorization
`heat_trace_factorization_seat`, the direct composite seat list
`spectralListCompSeat` with `e = eigComp`).

## The generator — a CHOICE, labeled CHOSEN on the face

The generator is **CHOSEN** as `H := (diracInst)²`, the square of
Q7CR-2's instantiated composite Dirac (`diracInst`,
`Q7C4R4Charge`). Nothing in this brick claims the dynamics was
derived or forced: `H` is a positive operator whose full spectral
data is landed (`dirac_sq_basisComp_eig`: `H` acts on
`basisComp t` as the scalar `eigComp t`), and the dynamics below
is defined SPECTRALLY through that landed eigenbasis — no
functional-calculus infrastructure is imported or fabricated.

## What is certified

- §1: the diagonal family `dynDiag` on `basisComp` and the heat
  family `dynHeat t = dynDiag (fun x => exp (-t * eigComp x))`,
  with `dynHeat 0 = 1` and the semigroup law
  `dynHeat (s + t) = dynHeat s * dynHeat t` (End multiplication,
  i.e. composition).
- §2: self-adjointness of every `dynHeat t` with respect to the
  registered composite pairing `compositePair` (Q7CR-1b's lifted
  pairing), in the exact form the landed basis supports:
  `basisComp` is `compositePair`-orthogonal with self-pairing
  `minkSign t.2 ∈ {+1, -1}` (the R⁴ factor's η-sign; the basis is
  orthogonal but NOT orthonormal for this pairing, and no
  orthonormality is claimed), and a `compositePair`-orthogonal
  diagonal operator with real eigenvalues is self-adjoint.
- §3: the coefficient formula for `dynHeat t` in `basisComp`
  coordinates and the spectral-floor contraction: for `t ≥ 0`
  every basis coefficient contracts by at least the floor rate
  `exp (-t / 64)` (eigenvalue-wise form on basis components —
  the form the landed basis supports; no pairing-norm operator
  bound is registered, since the pairing is the indefinite
  Minkowski-signed one of §2).
- §4: the Gibbs tie. `trace (dynHeat t) = ∑ x, exp (-t * eigComp x)`,
  the same sum as the multiset sum over `spectrumQ7CR2`, as SA2's
  seat heat object (`specSumIdx spectralListCompSeat.e … 1` and
  `specSumIdx spectralListSeat.e … 1`), and factorized as SA2's
  product of the three factor heat traces. The normalized weights
  `dynGibbs β` are the composite's Gibbs weights for `H`.
- §5: stationarity, this brick's own instance of the corpus's
  `gibbsWeight_stationary` pattern (`KMSBridge`): conjugation of
  any diagonal observable — in particular of the Gibbs operator
  itself — by the heat family returns it, and the Gibbs state on
  the eigenbasis is invariant under that flow.

## Named seam — the unitary form

**SEAM (unitary form, named, not faked):** no unitary
one-parameter family is registered by this brick. The composite
is a real space; the spectral phases of a unitary group would
need a complex structure on it, which the composite does not
carry as landed. The heat family `dynHeat` is THE dynamics
registered here; its §5 stationarity is the real, diagonal form
of the Gibbs stationarity the corpus owns over ℂ in
`KMSBridge`. No rotations on the real space are asserted.

## Fences

- Generator labeled CHOSEN (`H = D²` of the instantiated
  composite) on the face; no claim that dynamics was derived.
- No entropy language (the line's entropy consequences are
  gated elsewhere); none is stated here.
- Bounded-commutator vacuity caveat: in finite dimension that
  criterion is vacuous; not this brick's content.
- NO CLAIM; dials 0/4; no measured number.
-/

namespace ThetLogos

/-! ## §1. The CHOSEN generator, the diagonal family, the heat family -/

/-- **The CHOSEN generator** of the composite dynamics:
`H := (diracInst)²`, the square of the instantiated composite
Dirac. Label: **CHOSEN** — a positive operator with landed
spectral data, not a derived or forced generator. -/
noncomputable def dynGen : Module.End ℝ q7c4r4Composite :=
  diracInst ^ 2

/-- The generator acts on the landed eigenbasis by its landed
eigenvalues: `dynGen (basisComp t) = eigComp t • basisComp t`
(Q7CR-2's `dirac_sq_basisComp_eig`, transported along
`diracInst`'s definition). -/
theorem dynGen_basisComp (t : compIndex) :
    dynGen (basisComp t) = eigComp t • basisComp t :=
  dirac_sq_basisComp_eig t

/-- The diagonal family on the landed eigenbasis: `dynDiag w`
is the endomorphism acting on `basisComp x` as the scalar
`w x`, built by the basis's own constr. -/
noncomputable def dynDiag (w : compIndex → ℝ) :
    Module.End ℝ q7c4r4Composite :=
  basisComp.constr ℝ fun x => w x • basisComp x

/-- The diagonal family on basis vectors. -/
theorem dynDiag_apply_basis (w : compIndex → ℝ) (x : compIndex) :
    dynDiag w (basisComp x) = w x • basisComp x :=
  Module.Basis.constr_basis _ _ _ _

/-- **The heat family** of the CHOSEN generator, defined
spectrally through the landed eigenbasis: `dynHeat t` acts on
`basisComp x` as `exp (-t * eigComp x)`. This is the dynamics
registered by this brick (see the header's named seam on the
unitary form). -/
noncomputable def dynHeat (t : ℝ) : Module.End ℝ q7c4r4Composite :=
  dynDiag fun x => Real.exp (-t * eigComp x)

/-- The heat family on basis vectors. -/
theorem dynHeat_apply_basis (t : ℝ) (x : compIndex) :
    dynHeat t (basisComp x)
      = Real.exp (-t * eigComp x) • basisComp x :=
  dynDiag_apply_basis _ x

/-- The heat family at time `0` is the identity. -/
theorem dynHeat_zero : dynHeat 0 = 1 := by
  apply basisComp.ext
  intro x
  rw [dynHeat_apply_basis]
  simp

/-- The heat family at time `0`, in composition form. -/
theorem dynHeat_zero_apply (v : q7c4r4Composite) :
    dynHeat 0 v = v := by
  rw [dynHeat_zero]
  exact Module.End.one_apply v

/-- The semigroup law: `dynHeat (s + t) = dynHeat s * dynHeat t`
(End multiplication is composition), from exp additivity on
each eigencomponent. -/
theorem dynHeat_add (s t : ℝ) :
    dynHeat (s + t) = dynHeat s * dynHeat t := by
  apply basisComp.ext
  intro x
  rw [Module.End.mul_apply, dynHeat_apply_basis, dynHeat_apply_basis,
    map_smul, dynHeat_apply_basis, smul_smul]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- The heat family commutes with itself. -/
theorem dynHeat_comm (s t : ℝ) :
    dynHeat s * dynHeat t = dynHeat t * dynHeat s := by
  rw [← dynHeat_add, ← dynHeat_add, add_comm]

/-- Diagonal operators multiply pointwise on the eigenbasis. -/
theorem dynDiag_mul (w w' : compIndex → ℝ) :
    dynDiag w * dynDiag w' = dynDiag fun x => w x * w' x := by
  apply basisComp.ext
  intro x
  rw [Module.End.mul_apply, dynDiag_apply_basis, map_smul,
    dynDiag_apply_basis, dynDiag_apply_basis, smul_smul]
  congr 1
  exact mul_comm _ _

/-- Diagonal operators on the eigenbasis commute. -/
theorem dynDiag_comm (w w' : compIndex → ℝ) :
    dynDiag w * dynDiag w' = dynDiag w' * dynDiag w := by
  rw [dynDiag_mul, dynDiag_mul]
  congr 1
  funext x
  exact mul_comm _ _

/-- The heat family is a diagonal family with the Gibbs-shaped
weights at inverse temperature `β` (used in §5). -/
theorem dynHeat_eq_dynDiag (t : ℝ) :
    dynHeat t = dynDiag fun x => Real.exp (-t * eigComp x) :=
  rfl

/-! ## §2. The registered pairing on the landed basis; self-adjointness

The exact form the landed basis supports: `basisComp` is
orthogonal for the registered composite pairing `compositePair`,
with self-pairing the R⁴ η-sign (`minkSign`), and the pairing of
two arbitrary vectors is the `minkSign`-weighted diagonal sum of
their `basisComp` coordinates. Self-adjointness of `dynHeat t`
for `compositePair` follows from that diagonal form. -/

/-- The η-sign of an R⁴ site: `+1` at the time site `0`, `-1`
at the spatial sites. -/
def minkSign (m : Fin 4) : ℝ := if m = 0 then 1 else -1

/-- The η-sign is `+1` or `-1`. -/
theorem minkSign_eq (m : Fin 4) : minkSign m = 1 ∨ minkSign m = -1 := by
  by_cases h : m = 0 <;> simp [minkSign, h]

/-- The registered factor pairing in realified coordinates:
`factorPair n x y` is the plain dot product of the
real/imaginary-parts coordinates of `x` and `y`. -/
theorem factorPair_eq_sum_coords (n : ℕ) (x y : Fin n → ℂ) :
    factorPair n x y
      = ∑ a : Fin n × Fin 2, realBasisEquiv n x a
          * realBasisEquiv n y a := by
  have h0 : ∀ z : Fin n → ℂ, ∀ k : Fin n,
      realBasisEquiv n z (k, 0) = (z k).re := by
    intro z k
    show (if (0 : Fin 2) = 0 then (z k).re else (z k).im) = (z k).re
    rw [if_pos rfl]
  have h1 : ∀ z : Fin n → ℂ, ∀ k : Fin n,
      realBasisEquiv n z (k, 1) = (z k).im := by
    intro z k
    show (if (1 : Fin 2) = 0 then (z k).re else (z k).im) = (z k).im
    rw [if_neg (by decide)]
  unfold factorPair cplxPair
  rw [Complex.re_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_two, h0, h1, h0, h1]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-- The realified factor basis is orthonormal for the
registered factor pairing. -/
theorem factorPair_basisC (n : ℕ) (a a' : Fin n × Fin 2) :
    factorPair n (basisC n a) (basisC n a')
      = if a = a' then 1 else 0 := by
  have himg : ∀ c : Fin n × Fin 2,
      realBasisEquiv n (basisC n c) = Pi.single c 1 := by
    intro c
    unfold basisC
    rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Pi.basisFun_apply]
  rw [factorPair_eq_sum_coords, himg, himg]
  by_cases h : a = a'
  · subst h
    rw [if_pos rfl]
    simp [Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro c _
    rw [Pi.single_apply, Pi.single_apply]
    by_cases h1 : c = a
    · by_cases h2 : c = a'
      · exact absurd (h1.symm.trans h2) h
      · simp [h1, h2, h]
    · simp [h1]

/-- The Minkowski pairing on site vectors is the η-sign on the
diagonal and `0` off it. -/
theorem minkowskiInner_basisFun (m m' : Fin 4) :
    minkowskiInner ((Pi.basisFun ℝ (Fin 4)) m)
        ((Pi.basisFun ℝ (Fin 4)) m')
      = if m = m' then minkSign m else 0 := by
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  unfold minkowskiInner minkSign
  by_cases h : m = m'
  · subst h
    rw [if_pos rfl]
    fin_cases m <;> simp [Pi.single_apply] <;> norm_num
  · rw [if_neg h]
    have hz : ∀ j : Fin 4, (Pi.single m (1 : ℝ) : Fin 4 → ℝ) j
        * (Pi.single m' (1 : ℝ) : Fin 4 → ℝ) j = 0 := by
      intro j
      rw [Pi.single_apply, Pi.single_apply]
      by_cases hj : j = m
      · rw [if_pos hj, if_neg (fun hh => h (hj.symm.trans hh))]
        simp
      · rw [if_neg hj]
        simp
    simp [hz]

/-- **Orthogonality of the landed basis for the registered
pairing**: `compositePair (basisComp t) (basisComp u)` is
`minkSign t.2` on the diagonal and `0` off it. The basis is
orthogonal for `compositePair` but NOT orthonormal — the R⁴
factor contributes its η-sign — and this diagonal form is
exactly what §2's self-adjointness consumes. -/
theorem compositePair_basisComp (t u : compIndex) :
    compositePair (basisComp t) (basisComp u)
      = if t = u then minkSign t.2 else 0 := by
  obtain ⟨⟨a₇, a₄⟩, m⟩ := t
  obtain ⟨⟨b₇, b₄⟩, m'⟩ := u
  have hb : ∀ (x₇ : Fin 7 × Fin 2) (x₄ : Fin 4 × Fin 2) (xR : Fin 4),
      basisComp ((x₇, x₄), xR)
        = ((basisC 7 x₇ ⊗ₜ[ℝ] basisC 4 x₄)
            ⊗ₜ[ℝ] (Pi.basisFun ℝ (Fin 4)) xR) := by
    intro x₇ x₄ xR
    show Module.Basis.tensorProduct
        (Module.Basis.tensorProduct (basisC 7) (basisC 4))
        (Pi.basisFun ℝ (Fin 4)) ((x₇, x₄), xR) = _
    rw [Module.Basis.tensorProduct_apply,
      Module.Basis.tensorProduct_apply]
  rw [hb, hb, compositePair_tmul, factorPair_basisC,
    factorPair_basisC, minkowskiInner_basisFun]
  by_cases h₇ : a₇ = b₇ <;> by_cases h₄ : a₄ = b₄ <;>
    by_cases hm : m = m' <;>
    simp [h₇, h₄, hm, Prod.mk.injEq]

/-- The registered pairing is homogeneous in its first
argument (bilinearity, left slot). -/
theorem compositePair_smul_left (a : ℝ) (p q : q7c4r4Composite) :
    compositePair (a • p) q = a * compositePair p q := by
  simp [map_smul, smul_eq_mul]

/-- The registered pairing is homogeneous in its second
argument (bilinearity, right slot). -/
theorem compositePair_smul_right (a : ℝ) (p q : q7c4r4Composite) :
    compositePair p (a • q) = a * compositePair p q := by
  simp [map_smul, smul_eq_mul]

/-- The heat family in coordinates: expanding a vector in the
landed basis and flowing it. -/
theorem dynHeat_apply_formula (t : ℝ) (v : q7c4r4Composite) :
    dynHeat t v
      = ∑ x, (Real.exp (-t * eigComp x) * basisComp.repr v x)
          • basisComp x := by
  conv_lhs => rw [← basisComp.sum_repr v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul, dynHeat_apply_basis, smul_smul,
    mul_comm (basisComp.repr v x)]

/-- The coefficient formula: the `x`-th `basisComp` coordinate
of `dynHeat t v` is the `x`-th coordinate of `v` scaled by
`exp (-t * eigComp x)`. -/
theorem dynHeat_repr (t : ℝ) (v : q7c4r4Composite) (x : compIndex) :
    basisComp.repr (dynHeat t v) x
      = Real.exp (-t * eigComp x) * basisComp.repr v x := by
  rw [dynHeat_apply_formula]
  rw [map_sum]
  rw [Finsupp.finsetSum_apply]
  have hterm : ∀ y : compIndex,
      (basisComp.repr
        ((Real.exp (-t * eigComp y) * basisComp.repr v y)
          • basisComp y)) x
        = if y = x then Real.exp (-t * eigComp y)
            * basisComp.repr v y else 0 := by
    intro y
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases h : y = x <;> simp [h]
  rw [Finset.sum_congr rfl (fun y _ => hterm y),
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- **Self-adjointness of the heat family for the registered
composite pairing**, in the exact form the landed basis
supports: `dynHeat t` is diagonal in the
`compositePair`-orthogonal basis `basisComp` with real
eigenvalues, so the two bilinear forms `(v, w) ↦
compositePair (dynHeat t v) w` and `(v, w) ↦ compositePair v
(dynHeat t w)` agree on every basis pair — both are
`exp (-t * eigComp x)` times the diagonal pairing at `x = y`
and `0` off the diagonal — and bilinear forms agreeing on a
basis agree everywhere (`LinearMap.BilinForm.ext_iff_basis`). -/
theorem dynHeat_selfAdjoint (t : ℝ) (v w : q7c4r4Composite) :
    compositePair (dynHeat t v) w
      = compositePair v (dynHeat t w) := by
  have hB : (compositePair.flip.compl₂ (dynHeat t)).flip
      = compositePair.compl₂ (dynHeat t) := by
    rw [LinearMap.BilinForm.ext_iff_basis basisComp]
    intro x y
    show compositePair (dynHeat t (basisComp x)) (basisComp y)
      = compositePair (basisComp x) (dynHeat t (basisComp y))
    rw [dynHeat_apply_basis, dynHeat_apply_basis,
      compositePair_smul_left, compositePair_smul_right,
      compositePair_basisComp]
    by_cases h : x = y <;> simp [h]
  have happ := LinearMap.congr_fun
    (LinearMap.congr_fun hB v) w
  exact happ

/-! ## §3. Positivity and the spectral-floor contraction

The form the landed basis supports: eigenvalue-wise statements
on basis components. For `t ≥ 0` every heat eigenvalue
`exp (-t * eigComp x)` lies in `(0, 1]`, and every basis
coefficient of a flowed vector contracts by at least the floor
rate `exp (-t / 64)` — the landed spectral floor `1 / 64`
(`eigComp_ge`) is the *smallest* eigenvalue, so the floor rate
bounds every component, the ground eigenspace included. No
pairing-norm operator bound is registered: the registered
pairing is the indefinite Minkowski-signed one of §2. -/

/-- Heat eigenvalues are positive. -/
theorem dynHeat_eig_pos (t : ℝ) (x : compIndex) :
    0 < Real.exp (-t * eigComp x) :=
  Real.exp_pos _

/-- For `t ≥ 0`, heat eigenvalues are at most `1`. -/
theorem dynHeat_eig_le_one {t : ℝ} (ht : 0 ≤ t) (x : compIndex) :
    Real.exp (-t * eigComp x) ≤ 1 := by
  have hnn : -t * eigComp x ≤ 0 := by
    have h1 : (0 : ℝ) ≤ t * eigComp x :=
      mul_nonneg ht (le_trans (by norm_num) (eigComp_ge x))
    linarith
  calc Real.exp (-t * eigComp x) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr hnn
    _ = 1 := Real.exp_zero

/-- For `t ≥ 0`, heat eigenvalues lie in `(0, 1]`. -/
theorem dynHeat_eig_mem_Ioc {t : ℝ} (ht : 0 ≤ t) (x : compIndex) :
    Real.exp (-t * eigComp x) ∈ Set.Ioc 0 1 :=
  ⟨Real.exp_pos _, dynHeat_eig_le_one ht x⟩

/-- The floor rate bound: for `t ≥ 0`, every heat eigenvalue
is at most `exp (-t / 64)`, the exponential of the landed
spectral floor `1 / 64`. -/
theorem dynHeat_eig_le_floor {t : ℝ} (ht : 0 ≤ t) (x : compIndex) :
    Real.exp (-t * eigComp x) ≤ Real.exp (-t * (1 / 64)) := by
  apply Real.exp_le_exp.mpr
  have hle : t * (1 / 64) ≤ t * eigComp x :=
    mul_le_mul_of_nonneg_left (eigComp_ge x) ht
  linarith

/-- **Spectral-floor contraction, coefficient form**: for
`t ≥ 0`, every `basisComp` coefficient of `dynHeat t v` is at
most the floor rate `exp (-t / 64)` times the corresponding
coefficient of `v`, in absolute value. -/
theorem dynHeat_coeff_contract {t : ℝ} (ht : 0 ≤ t)
    (v : q7c4r4Composite) (x : compIndex) :
    |basisComp.repr (dynHeat t v) x|
      ≤ Real.exp (-t * (1 / 64)) * |basisComp.repr v x| := by
  rw [dynHeat_repr, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (dynHeat_eig_le_floor ht x)
    (abs_nonneg _)

/-! ## §4. The Gibbs tie: trace, partition function, Gibbs weights -/

/-- **The trace of the heat family**: `trace (dynHeat t)` is
the spectral sum of the heat weights over the landed
eigenvalues. -/
theorem dynHeat_trace (t : ℝ) :
    LinearMap.trace ℝ q7c4r4Composite (dynHeat t)
      = ∑ x, Real.exp (-t * eigComp x) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ basisComp]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro x _
  rw [LinearMap.toMatrix_apply, dynHeat_apply_basis]
  simp [Module.Basis.repr_self]

/-- The trace of the heat family, as the multiset sum over
Q7CR-2's landed spectrum multiset `spectrumQ7CR2`. -/
theorem dynHeat_trace_eq_spectrum_sum (t : ℝ) :
    LinearMap.trace ℝ q7c4r4Composite (dynHeat t)
      = (spectrumQ7CR2.map (fun v => Real.exp (-t * v))).sum := by
  rw [dynHeat_trace]
  unfold spectrumQ7CR2
  rw [Multiset.map_map]
  rfl

/-- The trace of the heat family is SA2's seat heat object:
the spectral-sum form of the action at the heat cutoff, over
SA2's direct composite seat list (`spectralListCompSeat`,
whose eigenvalue function is `eigComp`). -/
theorem dynHeat_trace_eq_compSeat_heat (t : ℝ) :
    LinearMap.trace ℝ q7c4r4Composite (dynHeat t)
      = specSumIdx spectralListCompSeat.e
          (fun x => Real.exp (-t * x)) 1 := by
  rw [dynHeat_trace]
  unfold specSumIdx
  apply Finset.sum_congr rfl
  intro x _
  have he : spectralListCompSeat.e = eigComp := rfl
  rw [he]
  simp

/-- **Heat-trace factorization for the dynamics**: the trace
of `dynHeat t` is the product of the three factor heat traces
at the seat — SA2's `heat_trace_factorization_seat` identity,
read off the dynamics' own trace. -/
theorem dynHeat_trace_factorization (t : ℝ) :
    LinearMap.trace ℝ q7c4r4Composite (dynHeat t)
      = specSum s₇ (fun x => Real.exp (-t * x)) 1
        * specSum s₄ (fun x => Real.exp (-t * x)) 1
        * specSum s_R (fun x => Real.exp (-t * x)) 1 := by
  have hexp : ∀ (a : Fin 7 × Fin 2) (b : Fin 4 × Fin 2) (m : Fin 4),
      Real.exp (-t * (s₇c a + s₄c b + s_R m))
        = Real.exp (-t * s₇c a) * Real.exp (-t * s₄c b)
          * Real.exp (-t * s_R m) := by
    intro a b m
    have h : -t * (s₇c a + s₄c b + s_R m)
        = (-t * s₇c a) + (-t * s₄c b) + (-t * s_R m) := by ring
    rw [h, Real.exp_add, Real.exp_add]
  have h2 : ∀ x : compIndex, Real.exp (-t * eigComp x)
      = Real.exp (-t * s₇c x.1.1) * Real.exp (-t * s₄c x.1.2)
        * Real.exp (-t * s_R x.2) := by
    intro x
    show Real.exp (-t * (s₇c x.1.1 + s₄c x.1.2 + s_R x.2)) = _
    exact hexp _ _ _
  have hsum : (∑ x : compIndex, Real.exp (-t * eigComp x))
      = (∑ a, Real.exp (-t * s₇c a))
        * (∑ b, Real.exp (-t * s₄c b))
        * (∑ m, Real.exp (-t * s_R m)) := by
    rw [Finset.sum_congr rfl (fun x _ => h2 x),
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    exact sum_triple_mul (fun a => Real.exp (-t * s₇c a))
      (fun b => Real.exp (-t * s₄c b))
      (fun m => Real.exp (-t * s_R m))
  have h7 : (∑ a, Real.exp (-t * s₇c a))
      = ∑ i, Real.exp (-t * s₇ i) :=
    (finProdFinEquiv (m := 7) (n := 2)).sum_comp
      (fun i => Real.exp (-t * s₇ i))
  have h4 : (∑ b, Real.exp (-t * s₄c b))
      = ∑ j, Real.exp (-t * s₄ j) :=
    (finProdFinEquiv (m := 4) (n := 2)).sum_comp
      (fun j => Real.exp (-t * s₄ j))
  rw [dynHeat_trace, hsum, h7, h4]
  unfold specSum
  simp

/-- The trace of the heat family is also SA2's tensored seat
heat object (`spectralListSeat`), by SA2's landed
factorization at the seat. -/
theorem dynHeat_trace_eq_seat_heat (t : ℝ) :
    LinearMap.trace ℝ q7c4r4Composite (dynHeat t)
      = specSumIdx spectralListSeat.e
          (fun x => Real.exp (-t * x)) 1 := by
  rw [dynHeat_trace_factorization, ← heat_trace_factorization_seat]

/-- **The partition function** of the CHOSEN generator: the
sum of the heat weights at inverse temperature `β` — the
trace of `dynHeat β` as a bare sum. -/
noncomputable def dynPartition (β : ℝ) : ℝ :=
  ∑ x, Real.exp (-β * eigComp x)

/-- The partition function is positive. -/
theorem dynPartition_pos (β : ℝ) : 0 < dynPartition β := by
  unfold dynPartition
  apply Finset.sum_pos
  · intro x _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- The partition function is the trace of the heat family. -/
theorem dynPartition_eq_trace (β : ℝ) :
    dynPartition β
      = LinearMap.trace ℝ q7c4r4Composite (dynHeat β) :=
  (dynHeat_trace β).symm

/-- **The composite's Gibbs weights for the CHOSEN generator
`H`**: the normalized heat weights in the landed eigenbasis. -/
noncomputable def dynGibbs (β : ℝ) (x : compIndex) : ℝ :=
  Real.exp (-β * eigComp x) / dynPartition β

/-- Gibbs weights are positive. -/
theorem dynGibbs_pos (β : ℝ) (x : compIndex) :
    0 < dynGibbs β x :=
  div_pos (Real.exp_pos _) (dynPartition_pos β)

/-- The Gibbs weights are normalized: they sum to `1`. -/
theorem dynGibbs_sum_eq_one (β : ℝ) :
    ∑ x, dynGibbs β x = 1 := by
  unfold dynGibbs
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (dynPartition_pos β))

/-- The Gibbs weights, unnormalized, are the heat family's
eigenvalues: `dynGibbs β x * dynPartition β = exp (-β *
eigComp x)`. -/
theorem dynGibbs_mul_partition (β : ℝ) (x : compIndex) :
    dynGibbs β x * dynPartition β
      = Real.exp (-β * eigComp x) := by
  unfold dynGibbs
  rw [div_mul_cancel₀ _ (ne_of_gt (dynPartition_pos β))]

/-! ## §5. Stationarity — this brick's own Gibbs instance

The finite Gibbs stationarity, in the form the corpus's landed
`gibbsWeight_stationary` (`KMSBridge`) takes over ℂ —
conjugation of the Gibbs operator by the flow it generates
returns it — proved here for the real diagonal dynamics:
conjugation by `dynHeat` rescales each eigencomponent's weight
by `exp (-s * eigComp x)` on one side and `exp (s * eigComp x)`
on the other, and the two cancel weight by weight. -/

/-- The Gibbs operator: the diagonal operator of the Gibbs
weights in the landed eigenbasis. -/
noncomputable def dynGibbsOp (β : ℝ) :
    Module.End ℝ q7c4r4Composite :=
  dynDiag (dynGibbs β)

/-- The cancellation at the heart of stationarity: flowing a
weight by `exp (-s * eigComp x)` and back by
`exp (s * eigComp x)` returns it. -/
theorem dynGibbs_weight_stationary (β s : ℝ) (x : compIndex) :
    Real.exp (-s * eigComp x) * dynGibbs β x
        * Real.exp (s * eigComp x)
      = dynGibbs β x := by
  have h1 : Real.exp (-s * eigComp x)
      * Real.exp (s * eigComp x) = 1 := by
    rw [← Real.exp_add]
    have hz : -s * eigComp x + s * eigComp x = 0 := by ring
    rw [hz, Real.exp_zero]
  calc Real.exp (-s * eigComp x) * dynGibbs β x
        * Real.exp (s * eigComp x)
      = (Real.exp (-s * eigComp x)
          * Real.exp (s * eigComp x)) * dynGibbs β x := by ring
    _ = dynGibbs β x := by rw [h1, one_mul]

/-- **Stationarity of the Gibbs operator**: conjugation by
the heat family returns the Gibbs operator of the CHOSEN
generator — this brick's own instance of the finite Gibbs
stationarity pattern. -/
theorem dynGibbs_stationary (β s : ℝ) :
    dynHeat s * dynGibbsOp β * dynHeat (-s) = dynGibbsOp β := by
  unfold dynGibbsOp
  rw [dynHeat_eq_dynDiag s, dynHeat_eq_dynDiag (-s),
    dynDiag_mul, dynDiag_mul]
  congr 1
  funext x
  have h2 : Real.exp (- -s * eigComp x)
      = Real.exp (s * eigComp x) := by
    congr 1
    ring
  rw [h2]
  exact dynGibbs_weight_stationary β s x

/-- The Gibbs operator commutes with the heat family it
generates (both are diagonal in the landed basis). -/
theorem dynHeat_dynGibbsOp_comm (β s : ℝ) :
    dynHeat s * dynGibbsOp β = dynGibbsOp β * dynHeat s :=
  dynDiag_comm _ _

/-- **The Gibbs state on the eigenbasis**: expectation of a
diagonal observable `a` (a weight function on `compIndex`)
against the Gibbs weights. -/
noncomputable def dynGibbsState (β : ℝ) (a : compIndex → ℝ) : ℝ :=
  ∑ x, dynGibbs β x * a x

/-- **Invariance of the Gibbs state under its own dynamics**:
flowing a diagonal observable's weights by the heat family
(the conjugation weights of `dynGibbs_stationary`) does not
change its Gibbs expectation. -/
theorem dynGibbsState_invariant (β s : ℝ) (a : compIndex → ℝ) :
    dynGibbsState β
        (fun x => Real.exp (-s * eigComp x) * a x
          * Real.exp (s * eigComp x))
      = dynGibbsState β a := by
  unfold dynGibbsState
  apply Finset.sum_congr rfl
  intro x _
  have h1 : Real.exp (-s * eigComp x)
      * Real.exp (s * eigComp x) = 1 := by
    rw [← Real.exp_add]
    have hz : -s * eigComp x + s * eigComp x = 0 := by ring
    rw [hz, Real.exp_zero]
  have hax : Real.exp (-s * eigComp x) * a x
      * Real.exp (s * eigComp x) = a x := by
    calc Real.exp (-s * eigComp x) * a x
          * Real.exp (s * eigComp x)
        = (Real.exp (-s * eigComp x)
            * Real.exp (s * eigComp x)) * a x := by ring
      _ = a x := by rw [h1, one_mul]
  show dynGibbs β x * (Real.exp (-s * eigComp x) * a x
      * Real.exp (s * eigComp x)) = dynGibbs β x * a x
  rw [hax]

end ThetLogos
