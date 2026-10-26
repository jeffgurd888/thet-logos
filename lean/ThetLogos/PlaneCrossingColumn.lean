/-
# ThetLogos.PlaneCrossingColumn — Brick β2-0: the single-column
obstruction, as a theorem

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. `(H-PF)` at general
`(G, ρ)` remains **L+ / open**. This module proves a NEGATIVE
statement about a *sub-object* of `layerKernel` (Brick β2's
`𝒜`): one layer column at frozen stratum values. It asserts
nothing about the sign of `𝒜` itself, which is untouched.

## The obstruction

Brick β1's factorization writes `𝒜`'s Boltzmann factor as a
product over the layer's columns (`exp_neg_layerAction_eq_prod`
below): pointwise in the stratum `α`,

  `exp (−layerAction ρ β α u u′) = ∏_{c, ν} columnKernel …`

where the column at `(c, ν)` is the exponential of one
plaquette density, whose word

  `W = a · u′ · b⁻¹ · u⁻¹,   a = α c,  b = α (σ_ν c)`

couples the two boundary faces through one trace — the factor
`b⁻¹ = (α (σ_ν c))⁻¹` sitting *between* `u′` and `u⁻¹` is the
weld of the β2 mechanism scoping (`beta2-mechanism-scoping`,
§2(b)). A proof of `𝒜 ⪰ 0` assembled column-by-column (each
frozen-stratum column factor a Gram / sum-of-squares kernel,
then products and Haar averages of PSD kernels, which are PSD)
would need every such column factor to be PSD. This module
proves that is false in general:

**`columnKernelSym_not_psd`** — at the finite seat
`G₀ = Multiplicative (ZMod 2)`, `ρ₀` = the sign character into
`unitaryGroup (Fin 1) ℂ`, `β = 1`, stratum values `a = 1`,
`b = seatS` (so the weld factor is `b⁻¹ = seatS`, of trace
value `−1`), the symmetrized single-column kernel has the
*explicit* pairing

  `∑_{u,u′} v u · κ_sym(u,u′) · v u′ = 2·e^{−2} − 2 < 0`

for the test vector `v` = the sign function itself. The kernel
is `[[e^{−2}, 1], [1, e^{−2}]]`, least eigenvalue `e^{−2} − 1`.
With the weld switched off (`b = 1`) the same computation
gives `[[1, e^{−2}], [e^{−2}, 1]]`, which is PSD: it is
exactly the weld's trace value `−1` that breaks the column.
(This is the T1 promotion of the seat computation's diagnostic
"fixed-a sums of squares are dead"; the (S₃, std) seat's
floating-point witnesses live in `crossing-sign-seats`.)

**Corollary (prose, labeled as such).** The formal content of
this module is the factorization (F) and the negative theorem
(N) above. The meta-consequence — *any* proof of `𝒜 ⪰ 0`
must use the joint stratum average essentially, since the
per-column implication "every frozen column factor is PSD"
already fails at one column — combines (F) and (N) with the
standard facts that Schur products and positive-measure
averages of PSD kernels are PSD. That combination is stated
here as prose, not as a Lean theorem.
-/

import ThetLogos.PlaneCrossingCube

namespace ThetLogos

open Finset

section ColumnKernel

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **Word density**: the corpus's one-plaquette Wilson density
as a function of the plaquette word alone:
`1 − (1/d) Re tr ρ(w)`. It is `plaquetteDensity` with the word
read off, cf. `plaquetteDensity_layerConfig_word`. -/
noncomputable def wordDensity (w : G) : ℝ :=
  1 - (Matrix.trace (repMatrix ρ w)).re / (d : ℝ)

/-- **The single-column kernel** `κ^{a,b}`: one layer column's
Boltzmann factor as a kernel on its boundary link values
`(u, u′)`, at frozen stratum values `a = α c`,
`b = α (σ_ν c)` — the exponential of `−β` times the density of
the column word `a · u′ · b⁻¹ · u⁻¹`. The factor `b⁻¹` between
`u′` and `u⁻¹` inside the single trace is the weld. -/
noncomputable def columnKernel (β : ℝ) (a b u u' : G) : ℝ :=
  Real.exp (-(β * wordDensity ρ (a * u' * b⁻¹ * u⁻¹)))

/-- The symmetrized single-column kernel — the Hermitian part,
the only part a quadratic form sees. -/
noncomputable def columnKernelSym (β : ℝ) (a b u u' : G) : ℝ :=
  (columnKernel ρ β a b u u' + columnKernel ρ β a b u' u) / 2

end ColumnKernel

section Factorization

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The column word, at the level of densities**: the
plaquette density of the layer configuration at `(c, ν)` is
the word density of Brick β1's column word
`α c · u′ ℓ · (α (σ_ν c))⁻¹ · u ℓ⁻¹`. -/
theorem plaquetteDensity_layerConfig_word (hN : Even N)
    (α : LayerSite N → G) (u u' : LayerLink N → G)
    (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν
      = wordDensity ρ (α c * u' (layerLinkOf c ν hν)
          * (α (layerShift ν hν c))⁻¹ * (u (layerLinkOf c ν hν))⁻¹) := by
  unfold plaquetteDensity wordDensity
  rw [plaquette_layerConfig hN α u u' c ν hν]

/-- **(F) The factorization through columns**: pointwise in
the stratum, `𝒜`'s Boltzmann factor is the product over the
layer's columns of the per-column Boltzmann factors. Together
with `plaquetteDensity_layerConfig_word`, each factor is a
`columnKernel` at that column's own data
`(α c, α (σ_ν c), u ℓ, u′ ℓ)`. -/
theorem exp_neg_layerAction_eq_prod (β : ℝ) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    Real.exp (-(layerAction ρ β α u u'))
      = ∏ c : LayerSite N, ∏ ν ∈ Finset.Ioi (0 : Fin 4),
          Real.exp (-(β * plaquetteDensity (torusShift N) ρ
            (layerConfig α u u') c.1 0 ν)) := by
  have hsum : -(layerAction ρ β α u u')
      = ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
          (-(β * plaquetteDensity (torusShift N) ρ
            (layerConfig α u u') c.1 0 ν)) := by
    unfold layerAction
    rw [← neg_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [neg_mul]
  rw [hsum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro c _
  rw [Real.exp_sum]

end Factorization

section Seat

/-- The nonidentity element of the seat group
`Multiplicative (ZMod 2)`. -/
def seatS : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem seatS_ne_one : seatS ≠ 1 := by
  intro h
  have h2 := congrArg Multiplicative.toAdd h
  simp only [seatS, toAdd_ofAdd, toAdd_one] at h2
  exact absurd h2 (by decide)

theorem seatS_mul_self : seatS * seatS = 1 := by
  apply Multiplicative.ext
  simp only [seatS, toAdd_mul, toAdd_ofAdd, toAdd_one]
  decide

theorem seatS_inv : seatS⁻¹ = seatS :=
  inv_eq_of_mul_eq_one_left seatS_mul_self

/-- Every element of the seat group is `1` or `seatS`. -/
theorem eq_one_or_seatS (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = seatS := by
  have hall : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases hall (Multiplicative.toAdd x) with h | h
  · left
    apply Multiplicative.ext
    rw [toAdd_one]
    exact h
  · right
    apply Multiplicative.ext
    simp only [seatS, toAdd_ofAdd]
    exact h

/-- The sign coefficient: `1` at the identity, `−1` at `seatS`,
as a complex number. -/
def signVal (x : Multiplicative (ZMod 2)) : ℂ := if x = 1 then 1 else -1

theorem signVal_one : signVal 1 = 1 := by simp [signVal]

theorem signVal_seatS : signVal seatS = -1 := by simp [signVal, seatS_ne_one]

theorem signVal_mul (x y : Multiplicative (ZMod 2)) :
    signVal (x * y) = signVal x * signVal y := by
  rcases eq_one_or_seatS x with rfl | rfl <;>
    rcases eq_one_or_seatS y with rfl | rfl <;>
    simp [signVal, seatS_mul_self, seatS_ne_one]

/-- The constant `Fin 1` matrix with entry `signVal x` — the
matrix of the seat representation at `x`. -/
def signMat (x : Multiplicative (ZMod 2)) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of (fun _ _ => signVal x)

theorem signMat_apply (x : Multiplicative (ZMod 2)) (i j : Fin 1) :
    signMat x i j = signVal x := rfl

theorem signMat_mul (x y : Multiplicative (ZMod 2)) :
    signMat (x * y) = signMat x * signMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signMat, Matrix.mul_apply, signVal_mul]

theorem signMat_one : signMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signMat, signVal_one]

theorem signMat_mem (x : Multiplicative (ZMod 2)) :
    signMat x ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  simp only [signMat_apply, Matrix.star_apply, Matrix.one_apply, ite_true]
  by_cases hx : x = 1 <;> simp [signVal, hx]

/-- **The seat representation** `ρ₀`: the sign character of
`Multiplicative (ZMod 2)` into `unitaryGroup (Fin 1) ℂ`. -/
def signRep : Multiplicative (ZMod 2) →*
    ↥(Matrix.unitaryGroup (Fin 1) ℂ) where
  toFun x := ⟨signMat x, signMat_mem x⟩
  map_one' := Subtype.ext signMat_one
  map_mul' x y := Subtype.ext (signMat_mul x y)

theorem repMatrix_signRep (x : Multiplicative (ZMod 2)) :
    repMatrix signRep x = signMat x := rfl

theorem signVal_re (w : Multiplicative (ZMod 2)) :
    (signVal w).re = if w = 1 then 1 else -1 := by
  by_cases hw : w = 1 <;> simp [signVal, hw]

/-- The word density at the seat is `0` at the identity and
`2` at `seatS` — the density sees only the sign of the word. -/
theorem wordDensity_signRep (w : Multiplicative (ZMod 2)) :
    wordDensity signRep w = if w = 1 then 0 else 2 := by
  have htr : Matrix.trace (repMatrix signRep w) = signVal w := by
    rw [repMatrix_signRep]
    simp [Matrix.trace, Matrix.diag, signMat_apply]
  unfold wordDensity
  rw [htr, signVal_re]
  split_ifs with hw <;> norm_num

/-- **The seat column kernel, explicitly**: at `β = 1`,
`a = 1`, `b = seatS`, the column kernel is `e^{−2}` on the
diagonal `u = u′` and `1` off it — it depends on `(u, u′)`
only through equality, so it is already symmetric. -/
theorem columnKernel_seat (u u' : Multiplicative (ZMod 2)) :
    columnKernel signRep 1 1 seatS u u'
      = if u = u' then Real.exp (-2) else 1 := by
  unfold columnKernel
  rcases eq_one_or_seatS u with rfl | rfl <;>
    rcases eq_one_or_seatS u' with rfl | rfl <;>
    simp [seatS_inv, seatS_mul_self, wordDensity_signRep, seatS_ne_one,
      Ne.symm seatS_ne_one]

/-- The symmetrized seat column kernel has the same explicit
form (the seat kernel is symmetric). -/
theorem columnKernelSym_seat (u u' : Multiplicative (ZMod 2)) :
    columnKernelSym signRep 1 1 seatS u u'
      = if u = u' then Real.exp (-2) else 1 := by
  unfold columnKernelSym
  rw [columnKernel_seat, columnKernel_seat]
  by_cases h : u = u'
  · rw [ite_eq_left h, ite_eq_left h.symm]; ring
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; norm_num

/-- The test vector: the sign function itself, as a real
vector on the seat group. -/
def seatVec (x : Multiplicative (ZMod 2)) : ℝ := if x = 1 then 1 else -1

theorem univ_seat :
    (Finset.univ : Finset (Multiplicative (ZMod 2))) = {1, seatS} := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_iff]
  exact eq_one_or_seatS x

/-- **The pairing, exactly**: the symmetrized seat column
kernel paired against the sign vector is `2·e^{−2} − 2`. -/
theorem columnKernelSym_pairing_eq :
    ∑ u, ∑ u', seatVec u * columnKernelSym signRep 1 1 seatS u u'
        * seatVec u'
      = 2 * Real.exp (-2) - 2 := by
  have h1s : (1 : Multiplicative (ZMod 2)) ≠ seatS := Ne.symm seatS_ne_one
  have e11 : columnKernelSym signRep 1 1 seatS 1 1 = Real.exp (-2) := by
    simp [columnKernelSym_seat]
  have e1s : columnKernelSym signRep 1 1 seatS 1 seatS = 1 := by
    simp [columnKernelSym_seat, h1s]
  have es1 : columnKernelSym signRep 1 1 seatS seatS 1 = 1 := by
    simp [columnKernelSym_seat, seatS_ne_one]
  have ess : columnKernelSym signRep 1 1 seatS seatS seatS
      = Real.exp (-2) := by
    simp [columnKernelSym_seat]
  have v1 : seatVec 1 = 1 := by simp [seatVec]
  have vs : seatVec seatS = -1 := by simp [seatVec, seatS_ne_one]
  rw [univ_seat]
  simp only [Finset.sum_pair h1s]
  rw [e11, e1s, es1, ess, v1, vs]
  ring

/-- The pairing is negative: `e^{−2} < 1`. -/
theorem columnKernelSym_pairing_neg :
    ∑ u, ∑ u', seatVec u * columnKernelSym signRep 1 1 seatS u u'
        * seatVec u' < 0 := by
  rw [columnKernelSym_pairing_eq]
  have he : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- **(N) The negative theorem (Brick β2-0's headline).** The
symmetrized single-column kernel is **not** positive
semidefinite in general: at the seat
`(Multiplicative (ZMod 2), signRep, β = 1, a = 1, b = seatS)`
there is a test vector — the sign function — whose pairing is
`2·e^{−2} − 2 < 0`. Hence no proof of `layerKernel ⪰ 0` can
be assembled from per-column PSD factors at frozen stratum:
any such proof must use the joint stratum average
essentially. This asserts nothing about `layerKernel`'s own
sign. -/
theorem columnKernelSym_not_psd :
    ¬ ∀ w : Multiplicative (ZMod 2) → ℝ,
      0 ≤ ∑ u, ∑ u', w u * columnKernelSym signRep 1 1 seatS u u'
        * w u' := by
  intro h
  have h0 := h seatVec
  rw [columnKernelSym_pairing_eq] at h0
  have he : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

end Seat

end ThetLogos
