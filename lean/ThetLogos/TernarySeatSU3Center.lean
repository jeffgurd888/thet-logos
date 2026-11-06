/-
# SU(3)-center bridge — C-0 pin (C-1 weld + C-2 computation follow)
(working label `TernarySeatSU3Center`; naming is Jeff's)

Commission: Jeff enrolled the SU(3)-center menu on 2026-11-05 20:44,
LAST in the enrolled queue (behind the Gram menu, the flow seat, and
the thermoelectric seat — all shipped). Charter: the scoping dossier
`~/workspace/your_files/ternary-seat-su3-center-scoping-2026-11-05.md`
(§§1–8), which governs wherever any summary of this module differs
from it.

**The question.** The Ternary Magnetism chain (TM-0..TM-4, shipped)
lives on the seat group `Multiplicative (ZMod 3)` with character
`seatChar₃`. ZMod 3 is also the center of SU(3) — but on the corpus's
SM side the center is ENTIRELY ABSENT (scoping §1.2: no `triality`
anywhere, no center computation, `SU3` a bare matrix group in
exactly one module; the pinned Mathlib supplies `Subgroup.center`'s
definition and no computation of this center). This module builds
the weld between the two wings.

## C-0 — the pin (this header; frozen working names and statements)

* `centerScalarSU3 : Multiplicative (ZMod 3) →* ↥SU3` — the scalar
  embedding, `g ↦ seatChar₃ g • (1 : Matrix (Fin 3) (Fin 3) ℂ)`
  packaged in `SU3` (C-1).
* `su3Inclusion : ↥SU3 →* ↥(Matrix.unitaryGroup (Fin 3) ℂ)` — the
  submonoid inclusion, the fundamental representation of the bare
  group, in the corpus's own `charFn` vocabulary.
* C-1 statements: `centerScalarSU3_coe_matrix` (the scalar-action
  form: `(centerScalarSU3 g : Matrix (Fin 3) (Fin 3) ℂ)
  = seatChar₃ g • 1`), `centerScalarSU3_mem_center` (range
  centrality: every `centerScalarSU3 g` lies in
  `Subgroup.center ↥SU3`), `charFn_centerScalarSU3` (the character
  weld: `charFn su3Inclusion (centerScalarSU3 g) = 3 * seatChar₃ g`).
* C-2 statements: `center_eq_range_centerScalarSU3`
  (`Subgroup.center ↥SU3 = (centerScalarSU3).range`, as subgroups of
  `↥SU3`) and the packaged isomorphism `su3CenterEquiv :
  Multiplicative (ZMod 3) ≃* ↥(Subgroup.center ↥SU3)`.
* C-3 (NOT this module; parent-side brick after integration): the
  filter re-read — for every pattern `ε`, `patternSurvives₃ ε ↔`
  invariance of the pattern monomial under the diagonal action of
  `↥(Subgroup.center ↥SU3)` transported along `su3CenterEquiv`, with
  site charge `patternDiv₃ ε c` (scoping §3.1).
* C-4 (NOT this module; OPTIONAL, parent-side): the center seat —
  transport of the TM chain's headline statements to
  `↥(Subgroup.center ↥SU3)` with the restricted fundamental rep
  (scoping §4.1). A re-dressing, honestly labeled; zero new
  mathematics claimed or expected.

## Kill register (armed on this face)

* **K-SU3-PI — PRE-FIRED, by T1 already on the books.** Any route of
  this weld through the corpus's represented picture (the Option-A
  representation `π`) is NOT STATEABLE: `pi_pure_color_zero`
  (`FiniteSpectralTriple.lean`) and `pi_ker_iff`
  (`SMGaugeAlgebra.lean`) prove that pure color acts as zero and
  that `ker π` is exactly the pure-color summand. The weld lives on
  the BARE group `SU3` and nowhere else, and this bridge must never
  be cited as closing `SMGaugeAlgebra` §4's priced gap (no
  independent represented SU(3) gauge action on quarks), which
  stands exactly as priced.
* **K-SU3-CENTER — armed for C-2, decided in this module.** Fires
  if `Subgroup.center ↥SU3` contains a non-scalar element.
  Mathematics says it will not fire; it is armed anyway, at full
  rank, because the corpus has so far *assumed* this in prose and
  never proved it.
* **K-SU3-FILTER — armed for C-3** (not decidable in this module).
* **K-SU3-TRANSPORT — armed for C-4** (not decidable in this
  module).

## Claim discipline (scoping §6, binding on every summary)

* Landing strengths, exact: C-1 buys "the seat character IS a
  center character of SU(3)" (the inclusion ⊆, not equality). C-2
  buys "the seat group IS the center of SU(3)", as a proved group
  isomorphism, with `seatChar₃` identified as the scalar character
  of the center action. The factor `3` in the C-1 weld is DIMENSION
  (the fundamental restricts to the center as `seatChar₃ ⊗ id₃` —
  three copies of the seat character — and the trace sees all
  three); it is stated here so it is never "discovered" later.
* The SM assembly's measured numbers (hypercharges, couplings,
  Yukawa entries, masses) remain **T2/T4 inputs** exactly as
  `SMFermions`/`SMLagrangian` record them; the weld derives none of
  them. `seatChar₃`'s values `{1, ω, ω²}` are phases of a finite
  character, not measured quantities — **no Dial-1 content**.
* Nothing about continuum QCD, confinement, glueballs, or the
  Yang–Mills mass gap follows. **NO CLAIM on every Millennium
  Problem stands.**
* Triality as a property of SU(3) *representations* remains
  unformalized (scoping §3.2: no SU(3) representation objects exist
  in-tree; `ColorRep` is a label carrying no group action). This
  bridge grades **seat patterns by center charge**, not quarks by
  N-ality.
* **Dial 2 = 0**: the weld contains no test body, no response law,
  no gravity object of any species.
* **NO CLAIM; dials 0/4 under every outcome.** A center-character
  weld is finite algebra.
-/

import ThetLogos.SMGaugeAlgebra
import ThetLogos.LayerKernelPosTernarySeat
import ThetLogos.PlaneCrossingKappa4Probe

namespace ThetLogos

/-! ## C-1 — the scalar embedding and the character weld

Landing strength, exact (scoping §2.3): **the seat character is a
center character of SU(3)** — `centerScalarSU3` maps the seat group
isomorphically onto a subgroup of the center, and `seatChar₃` is
the scalar of that action. C-1 proves ⊆, not `=`: that the center is
*nothing more* is C-2. -/

/-- The scalar matrix of a seat character lies in `SU3`: unitary
because `|seatChar₃ g| = 1` (the character's star-algebra), with
determinant `(seatChar₃ g)^3 = 1` because the dimension is `3` —
the same `3` as the seat's order. -/
theorem seatChar₃_smul_one_mem (g : Multiplicative (ZMod 3)) :
    seatChar₃ g • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ SU3 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · have hχ : seatChar₃ g * star (seatChar₃ g) = 1 := by
      rw [mul_comm]
      exact seatChar₃_star_mul_self g
    have hstar : star (seatChar₃ g • (1 : Matrix (Fin 3) (Fin 3) ℂ))
        = star (seatChar₃ g) • 1 := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one]
    rw [hstar, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, hχ, one_smul]
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rcases seatChar₃_cases g with h | h | h <;> rw [h]
    · norm_num
    · exact zetaC3_cube
    · have h6 : (zetaC3 ^ 2) ^ 3 = (zetaC3 ^ 3) ^ 2 := by ring
      rw [h6, zetaC3_cube]
      norm_num

/-- **C-1, the scalar embedding.** The seat group mapped into `SU3`
by scalar matrices: `g ↦ seatChar₃ g • I`. This lives on the bare
group `SU3` of `SMGaugeAlgebra` §1–§2 — never through the Option-A
representation `π` (K-SU3-PI, pre-fired). -/
noncomputable def centerScalarSU3 : Multiplicative (ZMod 3) →* ↥SU3 where
  toFun g := ⟨seatChar₃ g • 1, seatChar₃_smul_one_mem g⟩
  map_one' := by
    apply Subtype.ext
    show seatChar₃ (1 : Multiplicative (ZMod 3)) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = 1
    rw [seatChar₃_one, one_smul]
  map_mul' := by
    intro g h
    apply Subtype.ext
    show seatChar₃ (g * h) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = (seatChar₃ g • 1) * (seatChar₃ h • 1)
    rw [seatChar₃_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul]

/-- The inclusion of the bare group `SU3` into the unitary group —
the fundamental representation, in the corpus's `charFn`
vocabulary. -/
def su3Inclusion : ↥SU3 →* ↥(Matrix.unitaryGroup (Fin 3) ℂ) :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

/-- The scalar-action form of the embedding: as a matrix,
`centerScalarSU3 g` *is* the scalar `seatChar₃ g`. -/
theorem centerScalarSU3_coe_matrix (g : Multiplicative (ZMod 3)) :
    (centerScalarSU3 g : Matrix (Fin 3) (Fin 3) ℂ) = seatChar₃ g • 1 := rfl

/-- **C-1 (i), range centrality.** Every scalar matrix commutes with
every matrix, so the range of `centerScalarSU3` lies inside
`Subgroup.center ↥SU3`. -/
theorem centerScalarSU3_mem_center (g : Multiplicative (ZMod 3)) :
    centerScalarSU3 g ∈ Subgroup.center ↥SU3 := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  show (y : Matrix (Fin 3) (Fin 3) ℂ) * (seatChar₃ g • 1)
    = (seatChar₃ g • 1) * (y : Matrix (Fin 3) (Fin 3) ℂ)
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- **C-1 (ii), the character weld.** The corpus's own trace
character of the fundamental representation, evaluated at the
center element `centerScalarSU3 g`, is `3 * seatChar₃ g`. The `3`
is dimension: the fundamental restricts to the center as
`seatChar₃ ⊗ id₃`, and the trace sees all three copies. The weld
identifies `seatChar₃` with the **scalar** of the center action —
not with a second character. -/
theorem charFn_centerScalarSU3 (g : Multiplicative (ZMod 3)) :
    charFn su3Inclusion (centerScalarSU3 g) = 3 * seatChar₃ g := by
  show Matrix.trace (seatChar₃ g • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    = 3 * seatChar₃ g
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  simp [smul_eq_mul, mul_comm]

/-! ## C-2 — the center computation

**Route (scoping §5).** No lemma in the pinned Mathlib computes
this center, so the proof goes through explicit commuting families.
A central element's matrix commutes with every element of `SU3`;
commuting with the diagonal phase matrix `diag(1, ω, ω²)` — whose
entries are pairwise distinct — forces it **diagonal**; commuting
with the two signed permutation matrices (the phased swaps) then
forces the diagonal entries **equal**; the determinant condition
pins the common value to a **cube root of unity**; and the
cube-root classification (factoring over `zetaC3_sq_add` and
`zetaC3_cube`) identifies it as a value of `seatChar₃`.

**K-SU3-CENTER is DECIDED here: it does NOT fire.** No non-scalar
central element exists — every central element of `SU3` is
`ω^k • I` for a unique `k` — and the corpus no longer assumes this
in prose: `center_eq_range_centerScalarSU3` and `su3CenterEquiv`
are the proved statements.

Landing strength, exact (scoping §2.3): **the seat group IS the
center of SU(3)**, as a proved group isomorphism, and `seatChar₃`
is its defining character. -/

/-- `ω² ≠ 1` (else `ω = -2` by `zetaC3_sq_add`, against
`zetaC3_cube`). -/
theorem zetaC3_sq_ne_one : zetaC3 ^ 2 ≠ 1 := by
  intro h
  have h2 : zetaC3 = -2 := by
    have hs := zetaC3_sq_add
    rw [h] at hs
    linear_combination hs
  have h3 := zetaC3_cube
  rw [h2] at h3
  norm_num at h3

/-- `ω ≠ ω²` (else cancelling `ω ≠ 0` gives `ω = 1`). -/
theorem zetaC3_ne_sq : zetaC3 ≠ zetaC3 ^ 2 := by
  intro h
  have h2 : zetaC3 * 1 = zetaC3 * zetaC3 := by
    conv_rhs => rw [← pow_two]
    rwa [mul_one]
  have h3 := mul_left_cancel₀ zetaC3_ne_zero h2
  exact zetaC3_ne_one h3.symm

/-- The cube-root character of `ZMod 3` is faithful. -/
theorem chiC3_injective : Function.Injective chiC3 := by
  intro a b hab
  have hcases : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
  rcases hcases a with rfl | rfl | rfl <;> rcases hcases b with rfl | rfl | rfl <;>
    simp only [chiC3_zero, chiC3_one, chiC3_two] at hab
  · rfl
  · exact absurd hab.symm zetaC3_ne_one
  · exact absurd hab.symm zetaC3_sq_ne_one
  · exact absurd hab zetaC3_ne_one
  · rfl
  · exact absurd hab zetaC3_ne_sq
  · exact absurd hab zetaC3_sq_ne_one
  · exact absurd hab.symm zetaC3_ne_sq
  · rfl

/-- The seat character is faithful. -/
theorem seatChar₃_injective : Function.Injective seatChar₃ := by
  intro g h hgh
  have h2 : Multiplicative.toAdd g = Multiplicative.toAdd h :=
    chiC3_injective hgh
  exact Multiplicative.ofAdd.injective (by simpa using h2)

/-- The scalar embedding is faithful. -/
theorem centerScalarSU3_injective : Function.Injective centerScalarSU3 := by
  intro g h hgh
  have hmat : seatChar₃ g • (1 : Matrix (Fin 3) (Fin 3) ℂ)
      = seatChar₃ h • 1 := by
    have h2 := congrArg (fun x : ↥SU3 => (x : Matrix (Fin 3) (Fin 3) ℂ)) hgh
    rwa [centerScalarSU3_coe_matrix, centerScalarSU3_coe_matrix] at h2
  have h00 := congrFun (congrFun hmat 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  exact seatChar₃_injective h00

/-- A complex number with `c^3 = 1` is `1`, `ω`, or `ω²`: factor
`c^3 - 1 = (c - 1)(c^2 + c + 1)` and then
`c^2 + c + 1 = (c - ω)(c - ω^2)` over `zetaC3_sq_add` and
`zetaC3_cube`. -/
theorem cube_eq_one_cases (c : ℂ) (hc : c ^ 3 = 1) :
    c = 1 ∨ c = zetaC3 ∨ c = zetaC3 ^ 2 := by
  have hfact : (c - 1) * (c ^ 2 + c + 1) = 0 := by
    have h : (c - 1) * (c ^ 2 + c + 1) = c ^ 3 - 1 := by ring
    rw [h, hc, sub_self]
  rcases mul_eq_zero.mp hfact with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · have hfact2 : (c - zetaC3) * (c - zetaC3 ^ 2) = c ^ 2 + c + 1 := by
      linear_combination -c * zetaC3_sq_add + zetaC3_cube
    rw [← hfact2] at h2
    rcases mul_eq_zero.mp h2 with h3 | h4
    · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h4))

/-- The diagonal phase matrix `diag(1, ω, ω²)`: the commuting
family that forces a central matrix to be diagonal. -/
noncomputable def su3DiagMat : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![1, zetaC3, zetaC3 ^ 2]

theorem su3DiagMat_det : su3DiagMat.det = 1 := by
  rw [su3DiagMat, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ℂ) * zetaC3 * zetaC3 ^ 2 = zetaC3 ^ 3 by ring, zetaC3_cube]

theorem su3DiagMat_unitary : su3DiagMat * star su3DiagMat = 1 := by
  rw [su3DiagMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;>
    simp [Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zetaC3_star,
      star_pow]
  · rw [show zetaC3 * zetaC3 ^ 2 = zetaC3 ^ 3 by ring, zetaC3_cube]
  · rw [show zetaC3 ^ 2 * (zetaC3 ^ 2) ^ 2 = (zetaC3 ^ 3) ^ 2 by ring, zetaC3_cube]
    norm_num

/-- The diagonal phase matrix as an element of `SU3`. -/
noncomputable def su3DiagElt : ↥SU3 :=
  ⟨su3DiagMat, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr su3DiagMat_unitary, su3DiagMat_det⟩⟩

theorem su3DiagElt_coe :
    (su3DiagElt : Matrix (Fin 3) (Fin 3) ℂ) = su3DiagMat := rfl

theorem su3DiagMat_mul_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (su3DiagMat * A) i j = ![1, zetaC3, zetaC3 ^ 2] i * A i j := by
  rw [su3DiagMat, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hik
    rw [Matrix.diagonal_apply_ne _ hik.symm]
    exact zero_mul _
  · simp

theorem mul_su3DiagMat_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (A * su3DiagMat) i j = A i j * ![1, zetaC3, zetaC3 ^ 2] j := by
  rw [su3DiagMat, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hkj
    rw [Matrix.diagonal_apply_ne _ hkj]
    exact mul_zero _
  · simp

/-- The signed permutation matrix swapping axes `0, 1` (the `-1`
keeps the determinant at `1`): the commuting family that forces
the first two diagonal entries of a central matrix to agree. -/
def su3Swap01Mat : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![(0 : ℂ), 1, 0], ![1, 0, 0], ![0, 0, -1]]

theorem su3Swap01Mat_det : su3Swap01Mat.det = 1 := by
  rw [su3Swap01Mat, Matrix.det_fin_three]
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem su3Swap01Mat_unitary : su3Swap01Mat * star su3Swap01Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3Swap01Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The `0,1`-swap as an element of `SU3`. -/
noncomputable def su3Swap01Elt : ↥SU3 :=
  ⟨su3Swap01Mat, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr su3Swap01Mat_unitary, su3Swap01Mat_det⟩⟩

theorem su3Swap01Elt_coe :
    (su3Swap01Elt : Matrix (Fin 3) (Fin 3) ℂ) = su3Swap01Mat := rfl

/-- The signed permutation matrix swapping axes `1, 2`: the
commuting family that forces the last two diagonal entries of a
central matrix to agree. -/
def su3Swap12Mat : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![(-1 : ℂ), 0, 0], ![0, 0, 1], ![0, 1, 0]]

theorem su3Swap12Mat_det : su3Swap12Mat.det = 1 := by
  rw [su3Swap12Mat, Matrix.det_fin_three]
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem su3Swap12Mat_unitary : su3Swap12Mat * star su3Swap12Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3Swap12Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The `1,2`-swap as an element of `SU3`. -/
noncomputable def su3Swap12Elt : ↥SU3 :=
  ⟨su3Swap12Mat, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨Matrix.mem_unitaryGroup_iff.mpr su3Swap12Mat_unitary, su3Swap12Mat_det⟩⟩

theorem su3Swap12Elt_coe :
    (su3Swap12Elt : Matrix (Fin 3) (Fin 3) ℂ) = su3Swap12Mat := rfl

/-- **C-2, step 1: a central matrix is diagonal.** Commuting with
`su3DiagElt` equates, at entry `(i, j)`, the products
`d i * A i j` and `A i j * d j`; the diagonal values
`{1, ω, ω²}` are pairwise distinct, so off-diagonal entries
vanish. -/
theorem mem_center_apply_eq_zero {x : ↥SU3} (hx : x ∈ Subgroup.center ↥SU3)
    {i j : Fin 3} (hij : i ≠ j) :
    (x : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 := by
  have hcomm : ∀ y : ↥SU3, y * x = x * y := Subgroup.mem_center_iff.mp hx
  have hDA : su3DiagMat * (x : Matrix (Fin 3) (Fin 3) ℂ)
      = (x : Matrix (Fin 3) (Fin 3) ℂ) * su3DiagMat :=
    congrArg Subtype.val (hcomm su3DiagElt)
  have e := congrFun (congrFun hDA i) j
  rw [su3DiagMat_mul_apply, mul_su3DiagMat_apply] at e
  by_contra ha
  have e2 : ![1, zetaC3, zetaC3 ^ 2] i * (x : Matrix (Fin 3) (Fin 3) ℂ) i j
      = ![1, zetaC3, zetaC3 ^ 2] j * (x : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    rw [mul_comm (![1, zetaC3, zetaC3 ^ 2] j) ((x : Matrix (Fin 3) (Fin 3) ℂ) i j)]
    exact e
  have hdi := mul_right_cancel₀ ha e2
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · change (1 : ℂ) = zetaC3 at hdi
    exact absurd hdi.symm zetaC3_ne_one
  · change (1 : ℂ) = zetaC3 ^ 2 at hdi
    exact absurd hdi.symm zetaC3_sq_ne_one
  · change zetaC3 = (1 : ℂ) at hdi
    exact absurd hdi zetaC3_ne_one
  · exact absurd rfl hij
  · change zetaC3 = zetaC3 ^ 2 at hdi
    exact absurd hdi zetaC3_ne_sq
  · change zetaC3 ^ 2 = (1 : ℂ) at hdi
    exact absurd hdi zetaC3_sq_ne_one
  · change zetaC3 ^ 2 = zetaC3 at hdi
    exact absurd hdi.symm zetaC3_ne_sq
  · exact absurd rfl hij

/-- **C-2, step 2: a central matrix has constant diagonal.**
Commuting with the two signed swaps equates the diagonal entries
in pairs; off-diagonal entries vanish by step 1. -/
theorem mem_center_diag_eq {x : ↥SU3} (hx : x ∈ Subgroup.center ↥SU3) :
    (x : Matrix (Fin 3) (Fin 3) ℂ) 0 0 = (x : Matrix (Fin 3) (Fin 3) ℂ) 1 1
      ∧ (x : Matrix (Fin 3) (Fin 3) ℂ) 1 1
        = (x : Matrix (Fin 3) (Fin 3) ℂ) 2 2 := by
  have hcomm : ∀ y : ↥SU3, y * x = x * y := Subgroup.mem_center_iff.mp hx
  have hdiag : ∀ i j : Fin 3, i ≠ j → (x : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 :=
    fun i j hij => mem_center_apply_eq_zero hx hij
  constructor
  · have hS : su3Swap01Mat * (x : Matrix (Fin 3) (Fin 3) ℂ)
        = (x : Matrix (Fin 3) (Fin 3) ℂ) * su3Swap01Mat :=
      congrArg Subtype.val (hcomm su3Swap01Elt)
    have e := congrFun (congrFun hS 0) 1
    have eL : (su3Swap01Mat * (x : Matrix (Fin 3) (Fin 3) ℂ)) 0 1
        = (x : Matrix (Fin 3) (Fin 3) ℂ) 1 1 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single 1]
      · simp [su3Swap01Mat, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one]
      · intro k _ hk1
        rw [hdiag k 1 hk1, mul_zero]
      · simp
    have eR : ((x : Matrix (Fin 3) (Fin 3) ℂ) * su3Swap01Mat) 0 1
        = (x : Matrix (Fin 3) (Fin 3) ℂ) 0 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single 0]
      · simp [su3Swap01Mat, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one]
      · intro k _ hk0
        rw [hdiag 0 k hk0.symm, zero_mul]
      · simp
    rw [eL, eR] at e
    exact e.symm
  · have hS : su3Swap12Mat * (x : Matrix (Fin 3) (Fin 3) ℂ)
        = (x : Matrix (Fin 3) (Fin 3) ℂ) * su3Swap12Mat :=
      congrArg Subtype.val (hcomm su3Swap12Elt)
    have e := congrFun (congrFun hS 1) 2
    have eL : (su3Swap12Mat * (x : Matrix (Fin 3) (Fin 3) ℂ)) 1 2
        = (x : Matrix (Fin 3) (Fin 3) ℂ) 2 2 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single 2]
      · simp [su3Swap12Mat, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
      · intro k _ hk2
        rw [hdiag k 2 hk2, mul_zero]
      · simp
    have eR : ((x : Matrix (Fin 3) (Fin 3) ℂ) * su3Swap12Mat) 1 2
        = (x : Matrix (Fin 3) (Fin 3) ℂ) 1 1 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single 1]
      · simp [su3Swap12Mat, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
      · intro k _ hk1
        rw [hdiag 1 k hk1.symm, zero_mul]
      · simp
    rw [eL, eR] at e
    exact e.symm

/-- **C-2, step 3: a central matrix is a scalar matrix**, with the
scalar read off at entry `(0, 0)`. -/
theorem coe_eq_smul_of_mem_center {x : ↥SU3} (hx : x ∈ Subgroup.center ↥SU3) :
    (x : Matrix (Fin 3) (Fin 3) ℂ)
      = (x : Matrix (Fin 3) (Fin 3) ℂ) 0 0 • 1 := by
  rcases mem_center_diag_eq hx with ⟨h01, h12⟩
  ext i j
  by_cases h : i = j
  · subst h
    fin_cases i
    · simp [Matrix.smul_apply]
    · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      exact h01.symm
    · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      exact (h01.trans h12).symm
  · rw [mem_center_apply_eq_zero hx h, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_eq_mul, mul_zero]

/-- **C-2, the element form.** Every central element of `SU3` is a
scalar matrix whose scalar is a value of the seat character —
equivalently, every central element is in the range of
`centerScalarSU3`. This is the statement **K-SU3-CENTER** was armed
against: a non-scalar central element would appear here as a
counterexample, and none does. -/
theorem exists_centerScalarSU3_of_mem_center {x : ↥SU3}
    (hx : x ∈ Subgroup.center ↥SU3) :
    ∃ g : Multiplicative (ZMod 3), centerScalarSU3 g = x := by
  have hdet : (x : Matrix (Fin 3) (Fin 3) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp x.2).2
  have hscalar : (x : Matrix (Fin 3) (Fin 3) ℂ)
      = (x : Matrix (Fin 3) (Fin 3) ℂ) 0 0 • 1 :=
    coe_eq_smul_of_mem_center hx
  have hc3 : ((x : Matrix (Fin 3) (Fin 3) ℂ) 0 0) ^ 3 = 1 := by
    have h2 : ((x : Matrix (Fin 3) (Fin 3) ℂ) 0 0
        • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
        = ((x : Matrix (Fin 3) (Fin 3) ℂ) 0 0) ^ 3 := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [← hscalar] at h2
    rw [hdet] at h2
    exact h2.symm
  rcases cube_eq_one_cases _ hc3 with h1 | h1 | h1
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    show (centerScalarSU3 1 : Matrix (Fin 3) (Fin 3) ℂ)
      = (x : Matrix (Fin 3) (Fin 3) ℂ)
    rw [centerScalarSU3_coe_matrix, seatChar₃_one, hscalar, h1]
  · refine ⟨Multiplicative.ofAdd 1, ?_⟩
    apply Subtype.ext
    show (centerScalarSU3 (Multiplicative.ofAdd 1) : Matrix (Fin 3) (Fin 3) ℂ)
      = (x : Matrix (Fin 3) (Fin 3) ℂ)
    rw [centerScalarSU3_coe_matrix, seatChar₃_ofAdd_one, hscalar, h1]
  · refine ⟨Multiplicative.ofAdd 2, ?_⟩
    apply Subtype.ext
    show (centerScalarSU3 (Multiplicative.ofAdd 2) : Matrix (Fin 3) (Fin 3) ℂ)
      = (x : Matrix (Fin 3) (Fin 3) ℂ)
    rw [centerScalarSU3_coe_matrix, seatChar₃_ofAdd_two, hscalar, h1]

/-- **C-2, the center computation.** The center of `SU3` is exactly
the range of the scalar embedding: the seat group, embedded by
scalar matrices, *exhausts* the center. Together with C-1's
centrality this is the equality C-1 deliberately did not claim. -/
theorem center_eq_range_centerScalarSU3 :
    Subgroup.center ↥SU3 = centerScalarSU3.range := by
  ext x
  constructor
  · intro hx
    rcases exists_centerScalarSU3_of_mem_center hx with ⟨g, hg⟩
    exact ⟨g, hg⟩
  · intro hx
    rcases hx with ⟨g, rfl⟩
    exact centerScalarSU3_mem_center g

/-- **C-2, the packaged isomorphism.** The ternary seat's group
*is* the center of `SU3`, with `seatChar₃` as its defining
character. This is the iso C-3's transport is stated against. -/
noncomputable def su3CenterEquiv :
    Multiplicative (ZMod 3) ≃* ↥(Subgroup.center ↥SU3) :=
  MulEquiv.ofBijective
    (centerScalarSU3.codRestrict (Subgroup.center ↥SU3)
      fun g => centerScalarSU3_mem_center g)
    ⟨fun a b hab => centerScalarSU3_injective (congrArg Subtype.val hab),
     fun y => by
       rcases exists_centerScalarSU3_of_mem_center y.2 with ⟨g, hg⟩
       exact ⟨g, Subtype.ext hg⟩⟩

end ThetLogos
