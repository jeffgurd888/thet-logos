import ThetLogos.CFKernel22
import ThetLogos.SpectralActionFinite

/-!
# Vortex-locus pin (VL-2): P-VL1 — the commutator kernel at the thermal seat

Governing memo: `routeb-general-scratch/scoping-vortex-locus-2026-10-30.md`
(read in full; its §5 fences bind this module's language).  The VL-0 probe
is landed and registered as BR1-009 (exact-rational computation,
2026-10-30; independently re-confirmed 2026-11-01, identical):
at the seat below, the real commutator system over the `W22` span has
rank 12 and kernel dimension `d₀ = 10`.

**Objects (memo §5).**  A commutator map, its kernel, a centralizer
section over `W22`.  The locus is the flux-ZERO sector: the silent sector
of the `W22` geometry at its own thermal `K`, not a flow result and not
a stability result in any dynamical sense.  The words "vortex",
"hydrodynamic" and "circulation" are Jeff's T5 vocabulary and appear
here only in the module name inherited from the pin; no statement below
asserts that a Yukawa block "is" a circulation flux.

**Seat (T2 chosen inputs, stated on the face).**  `K0 = (smDirac 1 2 3 5 7)^2`,
i.e. `((β : ℂ)) • D^2` of `thermal_flux_vanishes` at `β = 1`,
`D = smDirac y₀` with `y₀ = (yNu, yE, yU, yD, yR) = (1, 2, 3, 5, 7)`
(real tuple).  The D-space is the `W22` submodule of `CFKernel22.lean`
(the real span of the 22 named directions `dirs22`; `dirs22_independent`,
`finrank_W22_le_22` and `cf_kernel_classification_46_22` are cited,
never reproved).  `K0`, `W22` and `dirs22` are cited from their landed
modules (`MartinettiRep.lean` for `smDirac`, `CFKernel22.lean` /
`CFKernelRetarget.lean` for the directions) — cited, never redefined.

**Headline (P-VL1, value exactly as registered by BR1-009).**
`Module.finrank ℝ (LinearMap.ker (commMap K0)) = 10`.
Any mismatch with 10 would be a stop-and-audit event, never a quiet
edit of the registered value.

**Proof route.**  `K0` is block-diagonal in the `blkIdx` decomposition
with diagonal `8 × 8` blocks (§2, the seat block forms).  A
`buildDirac` matrix whose Yukawa/Majorana blocks are diagonal commutes
with `K0` iff its Majorana diagonal `s` and Yukawa diagonal `u` satisfy
`s a = 7 * u a` at the single Majorana seat `a = 0` (§3); every kernel
direction of `dirs22` is of this form (§6).  The converse (§4, §10) reads
six entries of the commutator: they isolate the twelve non-kernel
coordinates and force the two relations `g 8 = 7 * g 0`, `g 9 = 7 * g 1`.

**NO CLAIM.**  Nothing here touches any Millennium statement; no dial
moves on any outcome.  The Props of the memo §1 are T2 as stated until
proved here; the seat `(y₀, β = 1, W22)` is a T2 chosen input.

No `sorry`, no `native_decide`.
-/

namespace ThetLogos

open Matrix

/-! ## §1. The seat and the commutator map -/

/-- The thermal seat of the pin: `K0 = (smDirac 1 2 3 5 7)^2`
(T2 chosen input; `β = 1` is inert for `β ≠ 0`). -/
def K0 : Matrix I32 I32 ℂ := (smDirac 1 2 3 5 7) ^ 2

/-- The commutator map at a fixed seat `K`, as a real-linear map on the
`W22` submodule: `X ↦ K * X − X * K`.  Its kernel is the centralizer
section of `K` over `W22` (equivalently the kernel of
`modularFlux K ·`, since `Complex.I ≠ 0`). -/
def commMap (K : Matrix I32 I32 ℂ) : W22 →ₗ[ℝ] Matrix I32 I32 ℂ where
  toFun X := K * X.val - X.val * K
  map_add' X Y := by
    show K * (X + Y).val - (X + Y).val * K
      = (K * X.val - X.val * K) + (K * Y.val - Y.val * K)
    rw [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
    simp only [sub_eq_add_neg, neg_add]
    ac_rfl
  map_smul' r X := by
    show K * (r • X).val - (r • X).val * K
      = r • (K * X.val - X.val * K)
    rw [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]

/-- The application form of `commMap`. -/
theorem commMap_apply (K : Matrix I32 I32 ℂ) (X : W22) :
    commMap K X = K * X.val - X.val * K := rfl

/-! ## §2. The seat block forms

The eight nonzero `8 × 8` blocks of `K0 = (smDirac 1 2 3 5 7)^2`
(cf. `pow2_buildDirac_blk_*` of `SpectralActionFinite.lean`) are
diagonal, with the two value vectors `![1, 4, 9, 25, 9, 25, 9, 25]`
(the squared Yukawa magnitudes `|w_a|^2`) and `![50, 4, 9, 25, 9, 25, 9, 25]`
(the same with the Majorana contribution `49` added at `a = 0`), and the
coupling blocks are `![7, 0, 0, 0, 0, 0, 0, 0]` (supported only at `a = 0`). -/

/-- Seat block (0,0): `A * Aᴴ` for `A = yukawaBlock 1 2 3 5`. -/
theorem seatAA : yukawaBlock 1 2 3 5 * (yukawaBlock 1 2 3 5).conjTranspose
    = Matrix.diagonal ![1, 4, 9, 25, 9, 25, 9, 25] := by
  unfold yukawaBlock
  rw [diag_mul_conjTranspose_diag]
  congr 1
  funext a
  fin_cases a <;> norm_num

/-- Seat block (0,3): `A * Eᴴ` for `E = majoranaBlock 7`. -/
theorem seatAE : yukawaBlock 1 2 3 5 * (majoranaBlock 7).conjTranspose
    = Matrix.diagonal ![7, 0, 0, 0, 0, 0, 0, 0] := by
  unfold yukawaBlock majoranaBlock
  rw [conjTranspose_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> norm_num

/-- Seat block (1,1): `Aᴴ * A + Eᴴ * E`. -/
theorem seat11 : (yukawaBlock 1 2 3 5).conjTranspose * yukawaBlock 1 2 3 5
    + (majoranaBlock 7).conjTranspose * majoranaBlock 7
    = Matrix.diagonal ![50, 4, 9, 25, 9, 25, 9, 25] := by
  unfold yukawaBlock majoranaBlock
  rw [conjTranspose_diagonal, conjTranspose_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, diagonal_add_eq]
  congr 1
  funext a
  fin_cases a <;> norm_num

/-- Seat block (1,2): `Eᴴ * Bᴴ` for `B = A.map (starRingEnd ℂ)`. -/
theorem seatEB : (majoranaBlock 7).conjTranspose
    * ((yukawaBlock 1 2 3 5).map (starRingEnd ℂ)).conjTranspose
    = Matrix.diagonal ![7, 0, 0, 0, 0, 0, 0, 0] := by
  unfold yukawaBlock majoranaBlock
  rw [Matrix.diagonal_map (by simp : (starRingEnd ℂ) 0 = 0), conjTranspose_diagonal,
    conjTranspose_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> norm_num [Function.comp, starRingEnd_apply]

/-- Seat block (2,1): `B * E`. -/
theorem seatBE : (yukawaBlock 1 2 3 5).map (starRingEnd ℂ) * majoranaBlock 7
    = Matrix.diagonal ![7, 0, 0, 0, 0, 0, 0, 0] := by
  unfold yukawaBlock majoranaBlock
  rw [Matrix.diagonal_map (by simp : (starRingEnd ℂ) 0 = 0), Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> norm_num [Function.comp, starRingEnd_apply]

/-- Seat block (2,2): `B * Bᴴ`. -/
theorem seatBB : (yukawaBlock 1 2 3 5).map (starRingEnd ℂ)
    * ((yukawaBlock 1 2 3 5).map (starRingEnd ℂ)).conjTranspose
    = Matrix.diagonal ![1, 4, 9, 25, 9, 25, 9, 25] := by
  unfold yukawaBlock
  rw [Matrix.diagonal_map (by simp : (starRingEnd ℂ) 0 = 0), conjTranspose_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> norm_num [Function.comp, starRingEnd_apply]

/-- Seat block (3,0): `E * Aᴴ`. -/
theorem seatEA : majoranaBlock 7 * (yukawaBlock 1 2 3 5).conjTranspose
    = Matrix.diagonal ![7, 0, 0, 0, 0, 0, 0, 0] := by
  unfold yukawaBlock majoranaBlock
  rw [conjTranspose_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> norm_num [Function.comp, starRingEnd_apply]

/-- Seat block (3,3): `E * Eᴴ + Bᴴ * B`. -/
theorem seat33 : majoranaBlock 7 * (majoranaBlock 7).conjTranspose
    + ((yukawaBlock 1 2 3 5).map (starRingEnd ℂ)).conjTranspose
      * (yukawaBlock 1 2 3 5).map (starRingEnd ℂ)
    = Matrix.diagonal ![50, 4, 9, 25, 9, 25, 9, 25] := by
  unfold yukawaBlock majoranaBlock
  rw [Matrix.diagonal_map (by simp : (starRingEnd ℂ) 0 = 0), conjTranspose_diagonal,
    conjTranspose_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    diagonal_add_eq]
  congr 1
  funext a
  fin_cases a <;> norm_num [Function.comp, starRingEnd_apply]

/-- The star-map of a diagonal matrix is diagonal. -/
theorem diagMapStar (u : Fin 8 → ℂ) : (Matrix.diagonal u).map (starRingEnd ℂ)
    = Matrix.diagonal (fun a => star (u a)) := by
  rw [Matrix.diagonal_map (by simp : (starRingEnd ℂ) 0 = 0)]
  rfl

/-- The conjugate transpose of the star-map of a diagonal matrix. -/
theorem diagMapStarCT (u : Fin 8 → ℂ) :
    ((Matrix.diagonal u).map (starRingEnd ℂ)).conjTranspose = Matrix.diagonal u := by
  rw [Matrix.diagonal_map (by simp : (starRingEnd ℂ) 0 = 0), conjTranspose_diagonal]
  congr 1
  funext a
  simp [Function.comp, star_star]


/-! ## §3. The diagonal-block commutation criterion

A `buildDirac` matrix whose Yukawa block `diagonal u` and Majorana block
`diagonal s` are diagonal commutes with `K0` iff the two diagonals are
linked at the single Majorana seat `a = 0` by `s a = 7 * u a` — the
coupling blocks of `K0` are supported only at `a = 0` (§2), and every
other block equation is a commutativity identity between diagonal
`8 × 8` matrices.  Only the forward (sufficient) direction is needed
and proved. -/


/-- Block entry (0,0) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_00 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 0 a1) (blkIdx 0 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (0,1) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_01 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 0 a1) (blkIdx 1 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (0,2) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_02 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 0 a1) (blkIdx 2 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (0,3) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_03 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 0 a1) (blkIdx 3 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (1,0) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_10 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 1 a1) (blkIdx 0 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (1,1) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_11 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 1 a1) (blkIdx 1 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (1,2) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_12 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 1 a1) (blkIdx 2 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (1,3) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_13 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 1 a1) (blkIdx 3 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (2,0) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_20 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 2 a1) (blkIdx 0 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (2,1) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_21 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 2 a1) (blkIdx 1 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (2,2) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_22 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 2 a1) (blkIdx 2 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (2,3) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_23 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 2 a1) (blkIdx 3 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (3,0) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_30 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 3 a1) (blkIdx 0 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (3,1) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_31 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 3 a1) (blkIdx 1 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (3,2) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_32 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 3 a1) (blkIdx 2 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- Block entry (3,3) of the commutator in `comm_buildDirac_diag`. -/
theorem comm_entry_33 (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    ∀ a1 a2 : Fin 8,
      ((smDirac 1 2 3 5 7) ^ 2 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
      - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2) (blkIdx 3 a1) (blkIdx 3 a2) = 0 := by
  intro a1 a2
  unfold smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Matrix.conjTranspose_zero,
    Finset.sum_const_zero, sub_self]
  try simp only [← Matrix.mul_apply]
  try simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33,
    diagMapStar, diagMapStarCT, conjTranspose_diagonal, Matrix.add_apply,
    Matrix.sub_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  try (by_cases h12 : a1 = a2
       · subst h12
         fin_cases a1 <;> simp [h] <;> ring
       · simp [h12, Ne.symm h12])

/-- The commutation criterion at the seat, in `smDirac`-square form. -/
theorem comm_buildDirac_diag (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    (smDirac 1 2 3 5 7) ^ 2
      * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
    - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * (smDirac 1 2 3 5 7) ^ 2 = 0 := by
  ext i j
  obtain ⟨b1, a1, hi⟩ : ∃ b : Fin 4, ∃ a : Fin 8, blkIdx b a = i :=
    ⟨⟨i.val / 8, by have hh := i.isLt; omega⟩, ⟨i.val % 8, by have hh := i.isLt; omega⟩,
      blkEquiv.right_inv i⟩
  obtain ⟨b2, a2, hj⟩ : ∃ b : Fin 4, ∃ a : Fin 8, blkIdx b a = j :=
    ⟨⟨j.val / 8, by have hh := j.isLt; omega⟩, ⟨j.val % 8, by have hh := j.isLt; omega⟩,
      blkEquiv.right_inv j⟩
  rw [← hi, ← hj]
  fin_cases b1 <;> fin_cases b2 <;> [exact comm_entry_00 u s h a1 a2; exact comm_entry_01 u s h a1 a2; exact comm_entry_02 u s h a1 a2; exact comm_entry_03 u s h a1 a2; exact comm_entry_10 u s h a1 a2; exact comm_entry_11 u s h a1 a2; exact comm_entry_12 u s h a1 a2; exact comm_entry_13 u s h a1 a2; exact comm_entry_20 u s h a1 a2; exact comm_entry_21 u s h a1 a2; exact comm_entry_22 u s h a1 a2; exact comm_entry_23 u s h a1 a2; exact comm_entry_30 u s h a1 a2; exact comm_entry_31 u s h a1 a2; exact comm_entry_32 u s h a1 a2; exact comm_entry_33 u s h a1 a2]

/-- The commutation criterion at the seat, in `K0` form. -/
theorem comm_K0_buildDirac_diag (u s : Fin 8 → ℂ)
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    K0 * buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s)
    - buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s) * K0 = 0 :=
  comm_buildDirac_diag u s h


/-! ## §4. Extraction: six entries of the commutator

For a general matrix `X`, six entries of `K0 * X - X * K0` are short
linear forms in entries of `X` (the seat blocks are diagonal, §2; the
coupling blocks contribute only through the `(24, ·)` / `(16, ·)` rows).
These six entries isolate the twelve non-kernel coordinates of §7. -/

/-- Extraction at entry `((0 : I32), (17 : I32))`. -/
theorem comm_entry_0_17 (X : Matrix I32 I32 ℂ) :
    (K0 * X - X * K0) (0 : I32) (17 : I32) = -3 * X (0 : I32) (17 : I32) + 7 * X (24 : I32) (17 : I32) := by
  show (K0 * X - X * K0) (blkIdx 0 0) (blkIdx 2 1) = -3 * X (blkIdx 0 0) (blkIdx 2 1) + 7 * X (blkIdx 3 0) (blkIdx 2 1)
  unfold K0 smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Finset.sum_const_zero]
  simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33]
  simp only [Fin.sum_univ_eight, Matrix.diagonal_apply]
  norm_num
  ring

/-- Extraction at entry `((2 : I32), (11 : I32))`. -/
theorem comm_entry_2_11 (X : Matrix I32 I32 ℂ) :
    (K0 * X - X * K0) (2 : I32) (11 : I32) = -16 * X (2 : I32) (11 : I32) := by
  show (K0 * X - X * K0) (blkIdx 0 2) (blkIdx 1 3) = -16 * X (blkIdx 0 2) (blkIdx 1 3)
  unfold K0 smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Finset.sum_const_zero]
  simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33]
  simp only [Fin.sum_univ_eight, Matrix.diagonal_apply]
  norm_num
  ring

/-- Extraction at entry `((3 : I32), (10 : I32))`. -/
theorem comm_entry_3_10 (X : Matrix I32 I32 ℂ) :
    (K0 * X - X * K0) (3 : I32) (10 : I32) = 16 * X (3 : I32) (10 : I32) := by
  show (K0 * X - X * K0) (blkIdx 0 3) (blkIdx 1 2) = 16 * X (blkIdx 0 3) (blkIdx 1 2)
  unfold K0 smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Finset.sum_const_zero]
  simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33]
  simp only [Fin.sum_univ_eight, Matrix.diagonal_apply]
  norm_num
  ring

/-- Extraction at entry `((0 : I32), (9 : I32))`. -/
theorem comm_entry_0_9 (X : Matrix I32 I32 ℂ) :
    (K0 * X - X * K0) (0 : I32) (9 : I32) = -3 * X (0 : I32) (9 : I32) + 7 * X (24 : I32) (9 : I32) := by
  show (K0 * X - X * K0) (blkIdx 0 0) (blkIdx 1 1) = -3 * X (blkIdx 0 0) (blkIdx 1 1) + 7 * X (blkIdx 3 0) (blkIdx 1 1)
  unfold K0 smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Finset.sum_const_zero]
  simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33]
  simp only [Fin.sum_univ_eight, Matrix.diagonal_apply]
  norm_num
  ring

/-- Extraction at entry `((8 : I32), (25 : I32))`. -/
theorem comm_entry_8_25 (X : Matrix I32 I32 ℂ) :
    (K0 * X - X * K0) (8 : I32) (25 : I32) = 46 * X (8 : I32) (25 : I32) + 7 * X (16 : I32) (25 : I32) := by
  show (K0 * X - X * K0) (blkIdx 1 0) (blkIdx 3 1) = 46 * X (blkIdx 1 0) (blkIdx 3 1) + 7 * X (blkIdx 2 0) (blkIdx 3 1)
  unfold K0 smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Finset.sum_const_zero]
  simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33]
  simp only [Fin.sum_univ_eight, Matrix.diagonal_apply]
  norm_num
  ring

/-- Extraction at entry `((0 : I32), (8 : I32))`. -/
theorem comm_entry_0_8 (X : Matrix I32 I32 ℂ) :
    (K0 * X - X * K0) (0 : I32) (8 : I32)
    = -49 * X (0 : I32) (8 : I32) + 7 * X (24 : I32) (8 : I32) - 7 * X (0 : I32) (16 : I32) := by
  show (K0 * X - X * K0) (blkIdx 0 0) (blkIdx 1 0)
    = -49 * X (blkIdx 0 0) (blkIdx 1 0) + 7 * X (blkIdx 3 0) (blkIdx 1 0)
      - 7 * X (blkIdx 0 0) (blkIdx 2 0)
  unfold K0 smDirac
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_blkIdx, sum_blkIdx,
    Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [pow2_buildDirac_blk_00, pow2_buildDirac_blk_03, pow2_buildDirac_blk_11,
    pow2_buildDirac_blk_12, pow2_buildDirac_blk_21, pow2_buildDirac_blk_22,
    pow2_buildDirac_blk_30, pow2_buildDirac_blk_33,
    pow2_buildDirac_blk_01_zero, pow2_buildDirac_blk_02_zero, pow2_buildDirac_blk_10_zero,
    pow2_buildDirac_blk_13_zero, pow2_buildDirac_blk_20_zero, pow2_buildDirac_blk_23_zero,
    pow2_buildDirac_blk_31_zero, pow2_buildDirac_blk_32_zero,
    mul_zero, zero_mul, add_zero, zero_add, Matrix.zero_apply, Finset.sum_const_zero]
  simp only [seatAA, seatAE, seat11, seatEB, seatBE, seatBB, seatEA, seat33]
  simp only [Fin.sum_univ_eight, Matrix.diagonal_apply]
  norm_num
  ring

/-! ## §5. Direction entries at the non-pivot positions

The corpus's pivot lemmas (`hva_*` / `hvb_*` / `hvan_*` of
`CFKernel22.lean`) cover seven of the eleven positions §7 reads.
The remaining four are computed here directly from the definitions. -/

/-- At `(0, 17)` every direction vanishes. -/
theorem dirs22_eq_zero_0_17 : ∀ k : Fin 22, dirs22 k (0 : I32) (17 : I32) = 0 := by
  intro k
  fin_cases k <;> simp [dirs22, dirs22Aux, smDirReNu, smDirImNu, smDirReE, smDirImE, smDirReU,
      smDirImU, smDirReD, smDirImD, smDirReR, smDirImR,
      exoticReNuLeR, exoticImNuLeR, exoticReELNuR, exoticImELNuR, exoticReULDR,
      exoticImULDR, exoticReDLUR, exoticImDLUR, exoticReNuREbarR, exoticImNuREbarR,
      exoticReEREbarR, exoticImEREbarR,
      smDirac, buildDirac, yukawaBlock, majoranaBlock]

/-- At `(0, 16)` every direction vanishes. -/
theorem dirs22_eq_zero_0_16 : ∀ k : Fin 22, dirs22 k (0 : I32) (16 : I32) = 0 := by
  intro k
  fin_cases k <;>
    simp [dirs22, dirs22Aux, smDirReNu, smDirImNu, smDirReE, smDirImE, smDirReU,
      smDirImU, smDirReD, smDirImD, smDirReR, smDirImR,
      exoticReNuLeR, exoticImNuLeR, exoticReELNuR, exoticImELNuR, exoticReULDR,
      exoticImULDR, exoticReDLUR, exoticImDLUR, exoticReNuREbarR, exoticImNuREbarR,
      exoticReEREbarR, exoticImEREbarR,
      smDirac, buildDirac, yukawaBlock, majoranaBlock]

/-- At `(24, 17)` only directions 12 (value `1`) and 13 (value `Complex.I`) are nonzero. -/
theorem dirs22_24_17 : ∀ k : Fin 22, dirs22 k (24 : I32) (17 : I32)
    = if k = 12 then 1 else if k = 13 then Complex.I else 0 := by
  intro k
  fin_cases k <;> simp [dirs22, dirs22Aux, smDirReNu, smDirImNu, smDirReE, smDirImE, smDirReU,
      smDirImU, smDirReD, smDirImD, smDirReR, smDirImR,
      exoticReNuLeR, exoticImNuLeR, exoticReELNuR, exoticImELNuR, exoticReULDR,
      exoticImULDR, exoticReDLUR, exoticImDLUR, exoticReNuREbarR, exoticImNuREbarR,
      exoticReEREbarR, exoticImEREbarR,
      smDirac, buildDirac, yukawaBlock, majoranaBlock]

/-- At `(24, 9)` only directions 18 (value `1`) and 19 (value `-Complex.I`) are nonzero. -/
theorem dirs22_24_9 : ∀ k : Fin 22, dirs22 k (24 : I32) (9 : I32)
    = if k = 18 then 1 else if k = 19 then -Complex.I else 0 := by
  intro k
  fin_cases k <;> simp [dirs22, dirs22Aux, smDirReNu, smDirImNu, smDirReE, smDirImE, smDirReU,
      smDirImU, smDirReD, smDirImD, smDirReR, smDirImR,
      exoticReNuLeR, exoticImNuLeR, exoticReELNuR, exoticImELNuR, exoticReULDR,
      exoticImULDR, exoticReDLUR, exoticImDLUR, exoticReNuREbarR, exoticImNuREbarR,
      exoticReEREbarR, exoticImEREbarR,
      smDirac, buildDirac, yukawaBlock, majoranaBlock]

/-- At `(16, 25)` only directions 10 (value `1`) and 11 (value `-Complex.I`) are nonzero. -/
theorem dirs22_16_25 : ∀ k : Fin 22, dirs22 k (16 : I32) (25 : I32)
    = if k = 10 then 1 else if k = 11 then -Complex.I else 0 := by
  intro k
  fin_cases k <;> simp [dirs22, dirs22Aux, smDirReNu, smDirImNu, smDirReE, smDirImE, smDirReU,
      smDirImU, smDirReD, smDirImD, smDirReR, smDirImR,
      exoticReNuLeR, exoticImNuLeR, exoticReELNuR, exoticImELNuR, exoticReULDR,
      exoticImULDR, exoticReDLUR, exoticImDLUR, exoticReNuREbarR, exoticImNuREbarR,
      exoticReEREbarR, exoticImEREbarR,
      smDirac, buildDirac, yukawaBlock, majoranaBlock]

/-- Reading the `a`-value off an if-form position lemma. -/
theorem hva_of_if {r c : I32} {a b : Fin 22} {z : ℂ}
    (hpos : ∀ k, dirs22 k r c = if k = a then (1 : ℂ) else if k = b then z else 0) :
    dirs22 a r c = 1 := by
  rw [hpos a]
  simp

/-- Reading the `b`-value off an if-form position lemma. -/
theorem hvb_of_if {r c : I32} {a b : Fin 22} {z : ℂ} (hab : a ≠ b)
    (hpos : ∀ k, dirs22 k r c = if k = a then (1 : ℂ) else if k = b then z else 0) :
    dirs22 b r c = z := by
  rw [hpos b, if_neg (Ne.symm hab), if_pos rfl]

/-- Reading the vanishing off an if-form position lemma. -/
theorem hvan_of_if {r c : I32} {a b : Fin 22} {z : ℂ}
    (hpos : ∀ k, dirs22 k r c = if k = a then (1 : ℂ) else if k = b then z else 0) :
    ∀ i, i ≠ a → i ≠ b → dirs22 i r c = 0 := by
  intro i h1 h2
  rw [hpos i]
  simp [h1, h2]


/-! ## §6. The kernel directions are diagonal-block `buildDirac` matrices

The two exotic kernel directions are `buildDirac` matrices with only a
Majorana block, and the two Nu/R kernel combinations are single
`smDirac` matrices — so §3's criterion applies to all ten kernel
directions of §7. -/

/-- `exoticReEREbarR` in diagonal-block `buildDirac` form. -/
theorem exoticReEREbarR_eq_buildDirac : exoticReEREbarR
    = buildDirac (Matrix.diagonal (0 : Fin 8 → ℂ))
        ((Matrix.diagonal (0 : Fin 8 → ℂ)).map (starRingEnd ℂ)) 0
        (Matrix.diagonal ![0, 1, 0, 0, 0, 0, 0, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exoticReEREbarR, buildDirac, Matrix.diagonal]

/-- `exoticImEREbarR` in diagonal-block `buildDirac` form. -/
theorem exoticImEREbarR_eq_buildDirac : exoticImEREbarR
    = buildDirac (Matrix.diagonal (0 : Fin 8 → ℂ))
        ((Matrix.diagonal (0 : Fin 8 → ℂ)).map (starRingEnd ℂ)) 0
        (Matrix.diagonal ![0, -Complex.I, 0, 0, 0, 0, 0, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exoticImEREbarR, buildDirac, Matrix.diagonal]

/-- The real Nu/R kernel combination `(1/7) • smDirReNu + smDirReR` is the single `smDirac (1/7) 0 0 0 1` (its parameters satisfy `yR = 7 * yNu`). -/
theorem smDirNuR_combo_re : (1/7 : ℝ) • smDirReNu + smDirReR = smDirac (1/7) 0 0 0 1 := by
  have e00 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 0 a1) (blkIdx 0 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 0 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e01 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 0 a1) (blkIdx 1 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 0 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e02 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 0 a1) (blkIdx 2 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 0 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e03 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 0 a1) (blkIdx 3 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 0 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e10 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 1 a1) (blkIdx 0 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 1 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e11 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 1 a1) (blkIdx 1 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 1 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e12 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 1 a1) (blkIdx 2 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 1 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e13 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 1 a1) (blkIdx 3 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 1 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e20 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 2 a1) (blkIdx 0 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 2 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e21 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 2 a1) (blkIdx 1 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 2 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e22 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 2 a1) (blkIdx 2 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 2 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e23 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 2 a1) (blkIdx 3 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 2 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e30 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 3 a1) (blkIdx 0 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 3 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e31 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 3 a1) (blkIdx 1 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 3 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e32 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 3 a1) (blkIdx 2 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 3 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e33 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirReNu + smDirReR) (blkIdx 3 a1) (blkIdx 3 a2)
      = (smDirac (1/7) 0 0 0 1) (blkIdx 3 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirReNu smDirReR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  ext i j
  obtain ⟨b1, a1, hi⟩ : ∃ b : Fin 4, ∃ a : Fin 8, blkIdx b a = i :=
    ⟨⟨i.val / 8, by have hh := i.isLt; omega⟩, ⟨i.val % 8, by have hh := i.isLt; omega⟩,
      blkEquiv.right_inv i⟩
  obtain ⟨b2, a2, hj⟩ : ∃ b : Fin 4, ∃ a : Fin 8, blkIdx b a = j :=
    ⟨⟨j.val / 8, by have hh := j.isLt; omega⟩, ⟨j.val % 8, by have hh := j.isLt; omega⟩,
      blkEquiv.right_inv j⟩
  rw [← hi, ← hj]
  fin_cases b1 <;> fin_cases b2 <;> [exact e00 a1 a2; exact e01 a1 a2; exact e02 a1 a2; exact e03 a1 a2; exact e10 a1 a2; exact e11 a1 a2; exact e12 a1 a2; exact e13 a1 a2; exact e20 a1 a2; exact e21 a1 a2; exact e22 a1 a2; exact e23 a1 a2; exact e30 a1 a2; exact e31 a1 a2; exact e32 a1 a2; exact e33 a1 a2]

/-- The imaginary Nu/R kernel combination `(1/7) • smDirImNu + smDirImR` is the single `smDirac (Complex.I/7) 0 0 0 Complex.I`. -/
theorem smDirNuR_combo_im : (1/7 : ℝ) • smDirImNu + smDirImR = smDirac (Complex.I/7) 0 0 0 Complex.I := by
  have e00 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 0 a1) (blkIdx 0 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 0 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e01 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 0 a1) (blkIdx 1 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 0 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e02 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 0 a1) (blkIdx 2 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 0 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e03 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 0 a1) (blkIdx 3 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 0 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e10 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 1 a1) (blkIdx 0 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 1 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e11 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 1 a1) (blkIdx 1 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 1 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e12 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 1 a1) (blkIdx 2 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 1 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e13 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 1 a1) (blkIdx 3 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 1 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e20 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 2 a1) (blkIdx 0 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 2 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e21 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 2 a1) (blkIdx 1 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 2 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e22 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 2 a1) (blkIdx 2 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 2 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e23 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 2 a1) (blkIdx 3 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 2 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e30 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 3 a1) (blkIdx 0 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 3 a1) (blkIdx 0 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e31 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 3 a1) (blkIdx 1 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 3 a1) (blkIdx 1 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e32 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 3 a1) (blkIdx 2 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 3 a1) (blkIdx 2 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  have e33 : ∀ a1 a2 : Fin 8,
      ((1/7 : ℝ) • smDirImNu + smDirImR) (blkIdx 3 a1) (blkIdx 3 a2)
      = (smDirac (Complex.I/7) 0 0 0 Complex.I) (blkIdx 3 a1) (blkIdx 3 a2) := by
    intro a1 a2
    rw [Matrix.add_apply, Matrix.smul_apply]
    unfold smDirImNu smDirImR smDirac
    simp only [buildDirac_blk_00, buildDirac_blk_01, buildDirac_blk_02, buildDirac_blk_03,
    buildDirac_blk_10, buildDirac_blk_11, buildDirac_blk_12, buildDirac_blk_13,
    buildDirac_blk_20, buildDirac_blk_21, buildDirac_blk_22, buildDirac_blk_23,
    buildDirac_blk_30, buildDirac_blk_31, buildDirac_blk_32, buildDirac_blk_33,
    yukawaBlock, majoranaBlock, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, starRingEnd_apply, Matrix.zero_apply, Matrix.conjTranspose_zero]
    by_cases h12 : a1 = a2
    · subst h12
      fin_cases a1 <;> simp [Algebra.smul_def] <;> norm_num [Complex.ext_iff]
    · simp [h12, Ne.symm h12]
  ext i j
  obtain ⟨b1, a1, hi⟩ : ∃ b : Fin 4, ∃ a : Fin 8, blkIdx b a = i :=
    ⟨⟨i.val / 8, by have hh := i.isLt; omega⟩, ⟨i.val % 8, by have hh := i.isLt; omega⟩,
      blkEquiv.right_inv i⟩
  obtain ⟨b2, a2, hj⟩ : ∃ b : Fin 4, ∃ a : Fin 8, blkIdx b a = j :=
    ⟨⟨j.val / 8, by have hh := j.isLt; omega⟩, ⟨j.val % 8, by have hh := j.isLt; omega⟩,
      blkEquiv.right_inv j⟩
  rw [← hi, ← hj]
  fin_cases b1 <;> fin_cases b2 <;> [exact e00 a1 a2; exact e01 a1 a2; exact e02 a1 a2; exact e03 a1 a2; exact e10 a1 a2; exact e11 a1 a2; exact e12 a1 a2; exact e13 a1 a2; exact e20 a1 a2; exact e21 a1 a2; exact e22 a1 a2; exact e23 a1 a2; exact e30 a1 a2; exact e31 a1 a2; exact e32 a1 a2; exact e33 a1 a2]


/-! ## §7. Coordinates on `W22`

`dirs22Combo g` is the vector with `dirs22`-coordinates `g`; every
element of `W22` has unique coordinates (`dirs22_independent`), so the
kernel of `commMap K0` is read off in coordinates in §8. -/

/-! ## §7. Coordinates on `W22`

`dirs22Combo g` is the vector with `dirs22`-coordinates `g`; every
element of `W22` has unique coordinates (`dirs22_independent`), so the
kernel of `commMap K0` is read off in coordinates in §8. -/

/-- The vector of `W22` with `dirs22`-coordinates `g`. -/
noncomputable def dirs22Combo (g : Fin 22 → ℝ) : W22 :=
  ⟨∑ k, g k • dirs22 k,
   sum_mem fun k _ => Submodule.smul_mem W22 (g k) (dirs22_mem_W22 k)⟩

/-- Entries of a coordinate combination. -/
theorem combo_entry (g : Fin 22 → ℝ) (r c : I32) :
    ((dirs22Combo g : W22) : Matrix I32 I32 ℂ) r c
      = ∑ k, g k • (dirs22 k r c) := by
  show (∑ k, g k • dirs22 k) r c = _
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_apply]

/-- A combination entry at a position where only the pair `a, b`
    (values `1` and general `z`) can be nonzero. -/
theorem combo_entry_pair_gen (g : Fin 22 → ℝ) {r c : I32} {a b : Fin 22} {z : ℂ}
    (hab : a ≠ b)
    (ha : dirs22 a r c = 1) (hb : dirs22 b r c = z)
    (hvan : ∀ i, i ≠ a → i ≠ b → dirs22 i r c = 0) :
    ((dirs22Combo g : W22) : Matrix I32 I32 ℂ) r c
      = (g a : ℂ) + (g b : ℂ) * z := by
  have hcollapse : ∀ {s : Finset (Fin 22)}, (∀ i ∈ s, i ≠ a → i ≠ b → dirs22 i r c = 0) →
      ∑ k ∈ s, g k • (dirs22 k r c)
        = ∑ k ∈ s ∩ {a, b}, g k • (dirs22 k r c) := by
    intro s hs
    apply (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro i his hi
    rw [Finset.mem_inter] at hi
    have hni : i ∉ ({a, b} : Finset (Fin 22)) := fun hm => hi ⟨his, hm⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hni
    push Not at hni
    obtain ⟨hia, hib⟩ := hni
    rw [hs i his hia hib, smul_zero]
  rw [combo_entry]
  have h2 : ∑ k ∈ (Finset.univ ∩ {a, b} : Finset (Fin 22)), g k • (dirs22 k r c)
      = g a • (dirs22 a r c) + g b • (dirs22 b r c) := by
    rw [Finset.univ_inter, Finset.sum_pair hab]
  rw [hcollapse (fun i _ => hvan i), h2, ha, hb]
  simp [Algebra.smul_def]

/-- A combination entry at a position where the pair values are `1` and `Complex.I`. -/
theorem combo_entry_pair (g : Fin 22 → ℝ) {r c : I32} {a b : Fin 22}
    (hab : a ≠ b)
    (ha : dirs22 a r c = 1) (hb : dirs22 b r c = Complex.I)
    (hvan : ∀ i, i ≠ a → i ≠ b → dirs22 i r c = 0) :
    ((dirs22Combo g : W22) : Matrix I32 I32 ℂ) r c
      = (g a : ℂ) + (g b : ℂ) * Complex.I := by
  have h := combo_entry_pair_gen g hab ha hb hvan
  simpa using h

/-- A combination entry at a position where all directions vanish. -/
theorem combo_entry_zero (g : Fin 22 → ℝ) {r c : I32}
    (hvan : ∀ i, dirs22 i r c = 0) :
    ((dirs22Combo g : W22) : Matrix I32 I32 ℂ) r c = 0 := by
  rw [combo_entry]
  exact Finset.sum_eq_zero fun k _ => by rw [hvan k, smul_zero]

/-! The coordinate map `(Fin 22 → ℝ) →ₗ[ℝ] W22` is an isomorphism. -/

/-- The coordinate linear map. -/
noncomputable def coordMap : (Fin 22 → ℝ) →ₗ[ℝ] W22 where
  toFun := dirs22Combo
  map_add' := by
    intro x y
    apply Subtype.ext
    show (∑ k, (x + y) k • dirs22 k) = _
    rw [Submodule.coe_add]
    show _ = (∑ k, x k • dirs22 k) + ∑ k, y k • dirs22 k
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.add_apply, add_smul]
  map_smul' := by
    intro r x
    apply Subtype.ext
    show (∑ k, (r • x) k • dirs22 k) = _
    rw [Submodule.coe_smul]
    show _ = r • ∑ k, x k • dirs22 k
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.smul_apply, smul_eq_mul, ← smul_smul]

/-- The coordinate map is injective (the directions are independent). -/
theorem coordMap_injective : Function.Injective coordMap := by
  have h := Fintype.linearIndependent_iff.mp dirs22_independent
  intro x y hxy
  funext k
  have h0 : ∑ i, (x - y) i • dirs22 i = 0 := by
    have h1 : coordMap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h2 : ((coordMap (x - y) : W22) : Matrix I32 I32 ℂ) = 0 := by
      rw [h1]; rfl
    exact h2
  have h4 := h (x - y) h0 k
  rw [Pi.sub_apply] at h4
  exact sub_eq_zero.mp h4

/-- `finrank ℝ W22 = 22`, from the injective coordinate map. -/
theorem finrank_W22_eq : Module.finrank ℝ W22 = 22 := by
  apply le_antisymm finrank_W22_le_22
  have h := LinearMap.finrank_le_finrank_of_injective coordMap_injective
  rwa [Module.finrank_pi, Fintype.card_fin] at h

/-- The coordinate isomorphism `(Fin 22 → ℝ) ≃ₗ[ℝ] W22`. -/
noncomputable def coordEquiv : (Fin 22 → ℝ) ≃ₗ[ℝ] W22 :=
  LinearEquiv.ofBijective coordMap
    ⟨coordMap_injective,
     (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
       (by rw [Module.finrank_pi, Fintype.card_fin, finrank_W22_eq])).mp
       coordMap_injective⟩

/-- The coordinate isomorphism computes as `dirs22Combo`. -/
theorem coordEquiv_apply (g : Fin 22 → ℝ) : coordEquiv g = dirs22Combo g :=
  LinearEquiv.ofBijective_apply coordMap g

/-- Coordinates of a single direction. -/
theorem coordEquiv_symm_single (k : Fin 22) :
    coordEquiv.symm ⟨dirs22 k, dirs22_mem_W22 k⟩ = Pi.single k 1 := by
  apply coordEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  rw [coordEquiv_apply]
  apply Subtype.ext
  show dirs22 k = ∑ i, (Pi.single k (1 : ℝ) : Fin 22 → ℝ) i • dirs22 i
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · simp


/-! ## §8. The ten kernel directions

`smDirac` in diagonal-block form (§6's criterion now applies to every
`smDirac`-shaped direction), and the ten kernel directions of the
registered basis: directions `2, …, 7`, the two Nu/R combinations with
`g8 = 7 * g0` resp. `g9 = 7 * g1`, and directions `20, 21`. -/

/-- `smDirac` in diagonal-block `buildDirac` form (its definition,
    with `yukawaBlock`/`majoranaBlock` unfolded). -/
theorem smDirac_eq_buildDirac_diag (p q r t w : ℂ) :
    smDirac p q r t w
    = buildDirac (Matrix.diagonal ![p, q, r, t, r, t, r, t])
        ((Matrix.diagonal ![p, q, r, t, r, t, r, t]).map (starRingEnd ℂ)) 0
        (Matrix.diagonal (fun k : Fin 8 => if k.val = 0 then w else 0)) := rfl

/-- Any element of `W22` whose matrix is a diagonal-block `buildDirac`
    satisfying the §3 link condition lies in `ker (commMap K0)`. -/
theorem mem_ker_of_val_eq (x : W22) (u s : Fin 8 → ℂ)
    (hx : (x : Matrix I32 I32 ℂ)
      = buildDirac (Matrix.diagonal u) ((Matrix.diagonal u).map (starRingEnd ℂ)) 0
        (Matrix.diagonal s))
    (h : ∀ a : Fin 8, a.val = 0 → s a = 7 * u a) :
    x ∈ LinearMap.ker (commMap K0) := by
  rw [LinearMap.mem_ker, commMap_apply, hx]
  exact comm_K0_buildDirac_diag u s h

/-- The single direction `kvDir k`, as an element of `W22`. -/
def kvDir (k : Fin 22) : W22 := ⟨dirs22 k, dirs22_mem_W22 k⟩

/-- Direction 2 (`smDirReE`) is in the kernel. -/
theorem kvDir_mem_ker_2 : kvDir 2 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![0, 1, 0, 0, 0, 0, 0, 0]
    (fun k : Fin 8 => if k.val = 0 then (0 : ℂ) else 0)
  · exact smDirac_eq_buildDirac_diag 0 1 0 0 0
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 3 (`smDirImE`) is in the kernel. -/
theorem kvDir_mem_ker_3 : kvDir 3 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![0, Complex.I, 0, 0, 0, 0, 0, 0]
    (fun k : Fin 8 => if k.val = 0 then (0 : ℂ) else 0)
  · exact smDirac_eq_buildDirac_diag 0 Complex.I 0 0 0
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 4 (`smDirReU`) is in the kernel. -/
theorem kvDir_mem_ker_4 : kvDir 4 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![0, 0, 1, 0, 1, 0, 1, 0]
    (fun k : Fin 8 => if k.val = 0 then (0 : ℂ) else 0)
  · exact smDirac_eq_buildDirac_diag 0 0 1 0 0
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 5 (`smDirImU`) is in the kernel. -/
theorem kvDir_mem_ker_5 : kvDir 5 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![0, 0, Complex.I, 0, Complex.I, 0, Complex.I, 0]
    (fun k : Fin 8 => if k.val = 0 then (0 : ℂ) else 0)
  · exact smDirac_eq_buildDirac_diag 0 0 Complex.I 0 0
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 6 (`smDirReD`) is in the kernel. -/
theorem kvDir_mem_ker_6 : kvDir 6 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![0, 0, 0, 1, 0, 1, 0, 1]
    (fun k : Fin 8 => if k.val = 0 then (0 : ℂ) else 0)
  · exact smDirac_eq_buildDirac_diag 0 0 0 1 0
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 7 (`smDirImD`) is in the kernel. -/
theorem kvDir_mem_ker_7 : kvDir 7 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![0, 0, 0, Complex.I, 0, Complex.I, 0, Complex.I]
    (fun k : Fin 8 => if k.val = 0 then (0 : ℂ) else 0)
  · exact smDirac_eq_buildDirac_diag 0 0 0 Complex.I 0
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 20 (`exoticReEREbarR`) is in the kernel. -/
theorem kvDir_mem_ker_20 : kvDir 20 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ (0 : Fin 8 → ℂ) ![0, 1, 0, 0, 0, 0, 0, 0]
  · exact exoticReEREbarR_eq_buildDirac
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- Direction 21 (`exoticImEREbarR`) is in the kernel. -/
theorem kvDir_mem_ker_21 : kvDir 21 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ (0 : Fin 8 → ℂ) ![0, -Complex.I, 0, 0, 0, 0, 0, 0]
  · exact exoticImEREbarR_eq_buildDirac
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    simp

/-- The real Nu/R combination `(1/7) • kvDir 0 + kvDir 8` is in the kernel. -/
theorem kvCombo_re_mem_ker :
    (1/7 : ℝ) • kvDir 0 + kvDir 8 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![1/7, 0, 0, 0, 0, 0, 0, 0]
    (fun k : Fin 8 => if k.val = 0 then (1 : ℂ) else 0)
  · exact smDirNuR_combo_re.trans (smDirac_eq_buildDirac_diag (1/7) 0 0 0 1)
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    norm_num [Matrix.cons_val_zero]

/-- The imaginary Nu/R combination `(1/7) • kvDir 1 + kvDir 9` is in the kernel. -/
theorem kvCombo_im_mem_ker :
    (1/7 : ℝ) • kvDir 1 + kvDir 9 ∈ LinearMap.ker (commMap K0) := by
  apply mem_ker_of_val_eq _ ![Complex.I/7, 0, 0, 0, 0, 0, 0, 0]
    (fun k : Fin 8 => if k.val = 0 then Complex.I else 0)
  · exact smDirNuR_combo_im.trans (smDirac_eq_buildDirac_diag (Complex.I/7) 0 0 0 Complex.I)
  · intro a ha
    have ha0 : a = 0 := Fin.ext ha
    subst ha0
    show Complex.I = 7 * (Complex.I / 7)
    rw [mul_comm, div_mul_cancel₀ _ (by norm_num : (7 : ℂ) ≠ 0)]

/-- The ten registered kernel directions, as a family on `Fin 10`. -/
noncomputable def kvFin : Fin 10 → W22 := ![kvDir 2, kvDir 3, kvDir 4, kvDir 5, kvDir 6, kvDir 7,
  (1/7 : ℝ) • kvDir 0 + kvDir 8, (1/7 : ℝ) • kvDir 1 + kvDir 9, kvDir 20, kvDir 21]

/-- Every `kvFin` direction lies in `ker (commMap K0)`. -/
theorem kvFin_mem_ker (j : Fin 10) : kvFin j ∈ LinearMap.ker (commMap K0) := by
  fin_cases j <;> [exact kvDir_mem_ker_2; exact kvDir_mem_ker_3; exact kvDir_mem_ker_4;
    exact kvDir_mem_ker_5; exact kvDir_mem_ker_6; exact kvDir_mem_ker_7;
    exact kvCombo_re_mem_ker; exact kvCombo_im_mem_ker; exact kvDir_mem_ker_20;
    exact kvDir_mem_ker_21]


/-! ## §9. Kernel = span of the ten directions

The general kernel combination `kvCombo g`, its matrix form, and the
identification `dirs22Combo g = kvCombo g` under the twelve coordinate
conditions of §10. -/

/-- The general kernel combination with coordinates `g` (in the form
    produced by the coordinate conditions). -/
noncomputable def kvCombo (g : Fin 22 → ℝ) : W22 :=
  g 2 • kvFin 0 + g 3 • kvFin 1 + g 4 • kvFin 2 + g 5 • kvFin 3 + g 6 • kvFin 4
    + g 7 • kvFin 5 + (7 * g 0) • kvFin 6 + (7 * g 1) • kvFin 7
    + g 20 • kvFin 8 + g 21 • kvFin 9

/-- Values of the single kernel directions. -/
theorem kvFin_zero_val : (kvFin 0).val = dirs22 2 := rfl
theorem kvFin_one_val : (kvFin 1).val = dirs22 3 := rfl
theorem kvFin_two_val : (kvFin 2).val = dirs22 4 := rfl
theorem kvFin_three_val : (kvFin 3).val = dirs22 5 := rfl
theorem kvFin_four_val : (kvFin 4).val = dirs22 6 := rfl
theorem kvFin_five_val : (kvFin 5).val = dirs22 7 := rfl
theorem kvFin_eight_val : (kvFin 8).val = dirs22 20 := rfl
theorem kvFin_nine_val : (kvFin 9).val = dirs22 21 := rfl

/-- Value of the real Nu/R kernel combination direction. -/
theorem kvFin_six_val : (kvFin 6).val = (1/7 : ℝ) • dirs22 0 + dirs22 8 := rfl

/-- Value of the imaginary Nu/R kernel combination direction. -/
theorem kvFin_seven_val : (kvFin 7).val = (1/7 : ℝ) • dirs22 1 + dirs22 9 := rfl

/-- The matrix of the general kernel combination. -/
theorem kvCombo_val (g : Fin 22 → ℝ) :
    (kvCombo g).val
    = g 2 • dirs22 2 + g 3 • dirs22 3 + g 4 • dirs22 4 + g 5 • dirs22 5
      + g 6 • dirs22 6 + g 7 • dirs22 7
      + (7 * g 0) • ((1/7 : ℝ) • dirs22 0 + dirs22 8)
      + (7 * g 1) • ((1/7 : ℝ) • dirs22 1 + dirs22 9)
      + g 20 • dirs22 20 + g 21 • dirs22 21 := by
  show (g 2 • kvFin 0 + g 3 • kvFin 1 + g 4 • kvFin 2 + g 5 • kvFin 3 + g 6 • kvFin 4
      + g 7 • kvFin 5 + (7 * g 0) • kvFin 6 + (7 * g 1) • kvFin 7
      + g 20 • kvFin 8 + g 21 • kvFin 9).val = _
  rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_add, Submodule.coe_add,
    Submodule.coe_add, Submodule.coe_add, Submodule.coe_add, Submodule.coe_add,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul,
    Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul,
    Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul,
    kvFin_zero_val, kvFin_one_val, kvFin_two_val, kvFin_three_val, kvFin_four_val,
    kvFin_five_val, kvFin_six_val, kvFin_seven_val, kvFin_eight_val, kvFin_nine_val]

/-- Expansion of a `Fin 22` sum of matrices into its 22 terms. -/
theorem sum_fin_22_matrix (F : Fin 22 → Matrix I32 I32 ℂ) :
    (∑ k, F k) = F 0 + F 1 + F 2 + F 3 + F 4 + F 5 + F 6 + F 7 + F 8 + F 9 + F 10
      + F 11 + F 12 + F 13 + F 14 + F 15 + F 16 + F 17 + F 18 + F 19 + F 20 + F 21 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- Under the twelve coordinate conditions, `dirs22Combo g = kvCombo g`. -/
theorem dirs22Combo_eq_kvCombo (g : Fin 22 → ℝ)
    (h8 : g 8 = 7 * g 0) (h9 : g 9 = 7 * g 1)
    (h10 : g 10 = 0) (h11 : g 11 = 0) (h12 : g 12 = 0) (h13 : g 13 = 0)
    (h14 : g 14 = 0) (h15 : g 15 = 0) (h16 : g 16 = 0) (h17 : g 17 = 0)
    (h18 : g 18 = 0) (h19 : g 19 = 0) :
    dirs22Combo g = kvCombo g := by
  apply Subtype.ext
  show (∑ k, g k • dirs22 k) = (kvCombo g).val
  rw [kvCombo_val, sum_fin_22_matrix]
  rw [h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  simp only [zero_smul, add_zero, zero_add]
  module


/-! ## §10. The kernel membership criterion (read-back for the locus)

A coordinate vector lies in `ker (commMap K0)` iff its twelve
non-kernel coordinates vanish or satisfy the two link relations.
This is the exact coordinate system of the locus: the free coordinates
are `g 0, g 1, g 2, …, g 7, g 20, g 21` (ten of them). -/

/-- Kernel membership in `dirs22` coordinates. -/
theorem dirs22Combo_mem_ker_iff (g : Fin 22 → ℝ) :
    dirs22Combo g ∈ LinearMap.ker (commMap K0) ↔
      g 12 = 0 ∧ g 13 = 0 ∧ g 14 = 0 ∧ g 15 = 0 ∧ g 16 = 0 ∧ g 17 = 0 ∧
      g 10 = 0 ∧ g 11 = 0 ∧ g 18 = 0 ∧ g 19 = 0 ∧
      g 8 = 7 * g 0 ∧ g 9 = 7 * g 1 := by
  constructor
  · intro h
    rw [LinearMap.mem_ker, commMap_apply] at h
    have e17 : (7 : ℂ) * ((g 12 : ℂ) + (g 13 : ℂ) * Complex.I) = 0 := by
      have e := congrFun (congrFun h (0 : I32)) (17 : I32)
      rw [comm_entry_0_17, combo_entry_zero g dirs22_eq_zero_0_17,
        combo_entry_pair g (show (12 : Fin 22) ≠ 13 by decide) (hva_of_if dirs22_24_17) (hvb_of_if (show (12 : Fin 22) ≠ 13 by decide) dirs22_24_17) (hvan_of_if dirs22_24_17)] at e
      simpa using e
    have q17 : (g 12 : ℂ) + (g 13 : ℂ) * Complex.I = 0 := by
      rcases mul_eq_zero.mp e17 with hcoef | hcoef
      · norm_num at hcoef
      · exact hcoef
    have hp17 : g 12 = 0 ∧ g 13 = 0 := by
      have ere := congrArg Complex.re q17
      have eim := congrArg Complex.im q17
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
      constructor <;> linarith
    have e211 : (-16 : ℂ) * ((g 14 : ℂ) + (g 15 : ℂ) * Complex.I) = 0 := by
      have e := congrFun (congrFun h (2 : I32)) (11 : I32)
      rw [comm_entry_2_11,
        combo_entry_pair g (show (14 : Fin 22) ≠ 15 by decide) hva_2_11 hvb_2_11 hvan_2_11] at e
      simpa using e
    have q211 : (g 14 : ℂ) + (g 15 : ℂ) * Complex.I = 0 := by
      rcases mul_eq_zero.mp e211 with hcoef | hcoef
      · norm_num at hcoef
      · exact hcoef
    have hp211 : g 14 = 0 ∧ g 15 = 0 := by
      have ere := congrArg Complex.re q211
      have eim := congrArg Complex.im q211
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
      constructor <;> linarith
    have e310 : (16 : ℂ) * ((g 16 : ℂ) + (g 17 : ℂ) * Complex.I) = 0 := by
      have e := congrFun (congrFun h (3 : I32)) (10 : I32)
      rw [comm_entry_3_10,
        combo_entry_pair g (show (16 : Fin 22) ≠ 17 by decide) hva_3_10 hvb_3_10 hvan_3_10] at e
      simpa using e
    have q310 : (g 16 : ℂ) + (g 17 : ℂ) * Complex.I = 0 := by
      rcases mul_eq_zero.mp e310 with hcoef | hcoef
      · norm_num at hcoef
      · exact hcoef
    have hp310 : g 16 = 0 ∧ g 17 = 0 := by
      have ere := congrArg Complex.re q310
      have eim := congrArg Complex.im q310
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
      constructor <;> linarith
    have e09 : (-3 : ℂ) * ((g 10 : ℂ) + (g 11 : ℂ) * Complex.I)
        + 7 * ((g 18 : ℂ) + (g 19 : ℂ) * (-Complex.I)) = 0 := by
      have e := congrFun (congrFun h (0 : I32)) (9 : I32)
      rw [comm_entry_0_9,
        combo_entry_pair g (show (10 : Fin 22) ≠ 11 by decide) hva_09 hvb_09 hvan_09,
        combo_entry_pair_gen g (show (18 : Fin 22) ≠ 19 by decide)
          (hva_of_if dirs22_24_9)
          (hvb_of_if (show (18 : Fin 22) ≠ 19 by decide) dirs22_24_9)
          (hvan_of_if dirs22_24_9)] at e
      simpa using e
    have e825 : (46 : ℂ) * ((g 18 : ℂ) + (g 19 : ℂ) * Complex.I)
        + 7 * ((g 10 : ℂ) + (g 11 : ℂ) * (-Complex.I)) = 0 := by
      have e := congrFun (congrFun h (8 : I32)) (25 : I32)
      rw [comm_entry_8_25,
        combo_entry_pair g (show (18 : Fin 22) ≠ 19 by decide) hva_8_25 hvb_8_25 hvan_8_25,
        combo_entry_pair_gen g (show (10 : Fin 22) ≠ 11 by decide)
          (hva_of_if dirs22_16_25)
          (hvb_of_if (show (10 : Fin 22) ≠ 11 by decide) dirs22_16_25)
          (hvan_of_if dirs22_16_25)] at e
      simpa using e
    have e08 : (-49 : ℂ) * ((g 0 : ℂ) + (g 1 : ℂ) * Complex.I)
        + 7 * ((g 8 : ℂ) + (g 9 : ℂ) * Complex.I) = 0 := by
      have e := congrFun (congrFun h (0 : I32)) (8 : I32)
      rw [comm_entry_0_8,
        combo_entry_pair g (show (0 : Fin 22) ≠ 1 by decide) hva_08 hvb_08 hvan_08,
        combo_entry_pair g (show (8 : Fin 22) ≠ 9 by decide) hva_24_8 hvb_24_8 hvan_24_8,
        combo_entry_zero g dirs22_eq_zero_0_16] at e
      simpa using e
    have r09 := congrArg Complex.re e09
    have i09 := congrArg Complex.im e09
    have r825 := congrArg Complex.re e825
    have i825 := congrArg Complex.im e825
    have r08 := congrArg Complex.re e08
    have i08 := congrArg Complex.im e08
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at r09 i09 r825 i825 r08 i08
    norm_num at r09 i09 r825 i825 r08 i08
    have h10 : g 10 = 0 := by linarith
    have h11 : g 11 = 0 := by linarith
    have h18 : g 18 = 0 := by linarith
    have h19 : g 19 = 0 := by linarith
    have h8 : g 8 = 7 * g 0 := by linarith
    have h9 : g 9 = 7 * g 1 := by linarith
    exact ⟨hp17.1, hp17.2, hp211.1, hp211.2, hp310.1, hp310.2,
      h10, h11, h18, h19, h8, h9⟩
  · intro hc
    obtain ⟨h12, h13, h14, h15, h16, h17, h10, h11, h18, h19, h8, h9⟩ := hc
    rw [dirs22Combo_eq_kvCombo g h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19]
    show (g 2 • kvFin 0 + g 3 • kvFin 1 + g 4 • kvFin 2 + g 5 • kvFin 3 + g 6 • kvFin 4
        + g 7 • kvFin 5 + (7 * g 0) • kvFin 6 + (7 * g 1) • kvFin 7
        + g 20 • kvFin 8 + g 21 • kvFin 9) ∈ LinearMap.ker (commMap K0)
    refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 0)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 1)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 2)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 3)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 4)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 5)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 6)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 7)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 8)
    · exact Submodule.smul_mem _ _ (kvFin_mem_ker 9)


/-! ## §11. Assembly

`ker (commMap K0) = span ℝ (range kvFin)`, the ten directions are
independent, and the registered dimension statement closes. -/

/-- The kernel is the span of the ten registered directions. -/
theorem ker_eq_span :
    LinearMap.ker (commMap K0) = Submodule.span ℝ (Set.range kvFin) := by
  apply le_antisymm
  · intro x hx
    set g := coordEquiv.symm x with hg
    have hxg : x = dirs22Combo g := by
      rw [← coordEquiv_apply g, hg]
      exact (LinearEquiv.apply_symm_apply coordEquiv x).symm
    rw [hxg] at hx
    obtain ⟨h12, h13, h14, h15, h16, h17, h10, h11, h18, h19, h8, h9⟩ :=
      (dirs22Combo_mem_ker_iff g).mp hx
    rw [hxg, dirs22Combo_eq_kvCombo g h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19]
    show (g 2 • kvFin 0 + g 3 • kvFin 1 + g 4 • kvFin 2 + g 5 • kvFin 3 + g 6 • kvFin 4
        + g 7 • kvFin 5 + (7 * g 0) • kvFin 6 + (7 * g 1) • kvFin 7
        + g 20 • kvFin 8 + g 21 • kvFin 9) ∈ Submodule.span ℝ (Set.range kvFin)
    refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 1))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 2))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 3))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 4))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 5))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 6))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 7))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 8))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 9))
  · rw [Submodule.span_le]
    intro y hy
    obtain ⟨j, rfl⟩ := hy
    exact kvFin_mem_ker j

/-- Expansion of a `Fin 10` sum of complex numbers into its ten terms. -/
theorem sum_fin_ten (F : Fin 10 → ℂ) :
    (∑ j, F j) = F 0 + F 1 + F 2 + F 3 + F 4 + F 5 + F 6 + F 7 + F 8 + F 9 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

/-- The ten registered kernel directions are linearly independent. -/
theorem kvFin_independent : LinearIndependent ℝ kvFin := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hentry : ∀ r c : I32, ∑ j, w j • ((kvFin j).val r c) = 0 := by
    intro r c
    have h := congrArg (fun x : W22 => ((x : Matrix I32 I32 ℂ))) hw
    rw [AddSubmonoid.coe_finset_sum] at h
    have h2 := congrFun (congrFun h r) c
    simpa [Matrix.sum_apply, Submodule.coe_smul, Submodule.coe_zero] using h2
  have kv0_19 : (kvFin 0).val (1 : I32) (9 : I32) = 1 := hva_19
  have kv1_19 : (kvFin 1).val (1 : I32) (9 : I32) = Complex.I := hvb_19
  have kv2_19 : (kvFin 2).val (1 : I32) (9 : I32) = 0 := hvan_19 4 (by decide) (by decide)
  have kv3_19 : (kvFin 3).val (1 : I32) (9 : I32) = 0 := hvan_19 5 (by decide) (by decide)
  have kv4_19 : (kvFin 4).val (1 : I32) (9 : I32) = 0 := hvan_19 6 (by decide) (by decide)
  have kv5_19 : (kvFin 5).val (1 : I32) (9 : I32) = 0 := hvan_19 7 (by decide) (by decide)
  have kv8_19 : (kvFin 8).val (1 : I32) (9 : I32) = 0 := hvan_19 20 (by decide) (by decide)
  have kv9_19 : (kvFin 9).val (1 : I32) (9 : I32) = 0 := hvan_19 21 (by decide) (by decide)
  have kv6_19 : (kvFin 6).val (1 : I32) (9 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 0 (1 : I32) (9 : I32) + dirs22 8 (1 : I32) (9 : I32) = 0
    rw [hvan_19 0 (by decide) (by decide), hvan_19 8 (by decide) (by decide),
      smul_zero, add_zero]
  have kv7_19 : (kvFin 7).val (1 : I32) (9 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 1 (1 : I32) (9 : I32) + dirs22 9 (1 : I32) (9 : I32) = 0
    rw [hvan_19 1 (by decide) (by decide), hvan_19 9 (by decide) (by decide),
      smul_zero, add_zero]
  have kv0_210 : (kvFin 0).val (2 : I32) (10 : I32) = 0 := hvan_2_10 2 (by decide) (by decide)
  have kv1_210 : (kvFin 1).val (2 : I32) (10 : I32) = 0 := hvan_2_10 3 (by decide) (by decide)
  have kv2_210 : (kvFin 2).val (2 : I32) (10 : I32) = 1 := hva_2_10
  have kv3_210 : (kvFin 3).val (2 : I32) (10 : I32) = Complex.I := hvb_2_10
  have kv4_210 : (kvFin 4).val (2 : I32) (10 : I32) = 0 := hvan_2_10 6 (by decide) (by decide)
  have kv5_210 : (kvFin 5).val (2 : I32) (10 : I32) = 0 := hvan_2_10 7 (by decide) (by decide)
  have kv8_210 : (kvFin 8).val (2 : I32) (10 : I32) = 0 := hvan_2_10 20 (by decide) (by decide)
  have kv9_210 : (kvFin 9).val (2 : I32) (10 : I32) = 0 := hvan_2_10 21 (by decide) (by decide)
  have kv6_210 : (kvFin 6).val (2 : I32) (10 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 0 (2 : I32) (10 : I32) + dirs22 8 (2 : I32) (10 : I32) = 0
    rw [hvan_2_10 0 (by decide) (by decide), hvan_2_10 8 (by decide) (by decide),
      smul_zero, add_zero]
  have kv7_210 : (kvFin 7).val (2 : I32) (10 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 1 (2 : I32) (10 : I32) + dirs22 9 (2 : I32) (10 : I32) = 0
    rw [hvan_2_10 1 (by decide) (by decide), hvan_2_10 9 (by decide) (by decide),
      smul_zero, add_zero]
  have kv0_311 : (kvFin 0).val (3 : I32) (11 : I32) = 0 := hvan_3_11 2 (by decide) (by decide)
  have kv1_311 : (kvFin 1).val (3 : I32) (11 : I32) = 0 := hvan_3_11 3 (by decide) (by decide)
  have kv2_311 : (kvFin 2).val (3 : I32) (11 : I32) = 0 := hvan_3_11 4 (by decide) (by decide)
  have kv3_311 : (kvFin 3).val (3 : I32) (11 : I32) = 0 := hvan_3_11 5 (by decide) (by decide)
  have kv4_311 : (kvFin 4).val (3 : I32) (11 : I32) = 1 := hva_3_11
  have kv5_311 : (kvFin 5).val (3 : I32) (11 : I32) = Complex.I := hvb_3_11
  have kv8_311 : (kvFin 8).val (3 : I32) (11 : I32) = 0 := hvan_3_11 20 (by decide) (by decide)
  have kv9_311 : (kvFin 9).val (3 : I32) (11 : I32) = 0 := hvan_3_11 21 (by decide) (by decide)
  have kv6_311 : (kvFin 6).val (3 : I32) (11 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 0 (3 : I32) (11 : I32) + dirs22 8 (3 : I32) (11 : I32) = 0
    rw [hvan_3_11 0 (by decide) (by decide), hvan_3_11 8 (by decide) (by decide),
      smul_zero, add_zero]
  have kv7_311 : (kvFin 7).val (3 : I32) (11 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 1 (3 : I32) (11 : I32) + dirs22 9 (3 : I32) (11 : I32) = 0
    rw [hvan_3_11 1 (by decide) (by decide), hvan_3_11 9 (by decide) (by decide),
      smul_zero, add_zero]
  have kv0_925 : (kvFin 0).val (9 : I32) (25 : I32) = 0 := hvan_9_25 2 (by decide) (by decide)
  have kv1_925 : (kvFin 1).val (9 : I32) (25 : I32) = 0 := hvan_9_25 3 (by decide) (by decide)
  have kv2_925 : (kvFin 2).val (9 : I32) (25 : I32) = 0 := hvan_9_25 4 (by decide) (by decide)
  have kv3_925 : (kvFin 3).val (9 : I32) (25 : I32) = 0 := hvan_9_25 5 (by decide) (by decide)
  have kv4_925 : (kvFin 4).val (9 : I32) (25 : I32) = 0 := hvan_9_25 6 (by decide) (by decide)
  have kv5_925 : (kvFin 5).val (9 : I32) (25 : I32) = 0 := hvan_9_25 7 (by decide) (by decide)
  have kv8_925 : (kvFin 8).val (9 : I32) (25 : I32) = 1 := hva_9_25
  have kv9_925 : (kvFin 9).val (9 : I32) (25 : I32) = Complex.I := hvb_9_25
  have kv6_925 : (kvFin 6).val (9 : I32) (25 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 0 (9 : I32) (25 : I32) + dirs22 8 (9 : I32) (25 : I32) = 0
    rw [hvan_9_25 0 (by decide) (by decide), hvan_9_25 8 (by decide) (by decide),
      smul_zero, add_zero]
  have kv7_925 : (kvFin 7).val (9 : I32) (25 : I32) = 0 := by
    show (1/7 : ℝ) • dirs22 1 (9 : I32) (25 : I32) + dirs22 9 (9 : I32) (25 : I32) = 0
    rw [hvan_9_25 1 (by decide) (by decide), hvan_9_25 9 (by decide) (by decide),
      smul_zero, add_zero]
  have kv0_08 : (kvFin 0).val (0 : I32) (8 : I32) = 0 := hvan_08 2 (by decide) (by decide)
  have kv1_08 : (kvFin 1).val (0 : I32) (8 : I32) = 0 := hvan_08 3 (by decide) (by decide)
  have kv2_08 : (kvFin 2).val (0 : I32) (8 : I32) = 0 := hvan_08 4 (by decide) (by decide)
  have kv3_08 : (kvFin 3).val (0 : I32) (8 : I32) = 0 := hvan_08 5 (by decide) (by decide)
  have kv4_08 : (kvFin 4).val (0 : I32) (8 : I32) = 0 := hvan_08 6 (by decide) (by decide)
  have kv5_08 : (kvFin 5).val (0 : I32) (8 : I32) = 0 := hvan_08 7 (by decide) (by decide)
  have kv8_08 : (kvFin 8).val (0 : I32) (8 : I32) = 0 := hvan_08 20 (by decide) (by decide)
  have kv9_08 : (kvFin 9).val (0 : I32) (8 : I32) = 0 := hvan_08 21 (by decide) (by decide)
  have kv6_08 : (kvFin 6).val (0 : I32) (8 : I32) = (1/7 : ℝ) • (1 : ℂ) := by
    show (1/7 : ℝ) • dirs22 0 (0 : I32) (8 : I32) + dirs22 8 (0 : I32) (8 : I32) = _
    rw [hva_08, hvan_08 8 (by decide) (by decide), add_zero]
  have kv7_08 : (kvFin 7).val (0 : I32) (8 : I32) = (1/7 : ℝ) • Complex.I := by
    show (1/7 : ℝ) • dirs22 1 (0 : I32) (8 : I32) + dirs22 9 (0 : I32) (8 : I32) = _
    rw [hvb_08, hvan_08 9 (by decide) (by decide), add_zero]

  have p19 : w 0 = 0 ∧ w 1 = 0 := by
    have h := hentry 1 9
    rw [sum_fin_ten, kv0_19, kv1_19, kv2_19, kv3_19, kv4_19, kv5_19, kv6_19, kv7_19, kv8_19, kv9_19] at h
    simp only [smul_zero, add_zero, zero_add] at h
    have h' : (w 0 : ℂ) * 1 + (w 1 : ℂ) * Complex.I = 0 := h
    have ere := congrArg Complex.re h'
    have eim := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
    norm_num at ere eim
    constructor <;> linarith
  have p210 : w 2 = 0 ∧ w 3 = 0 := by
    have h := hentry 2 10
    rw [sum_fin_ten, kv0_210, kv1_210, kv2_210, kv3_210, kv4_210, kv5_210, kv6_210, kv7_210, kv8_210, kv9_210] at h
    simp only [smul_zero, add_zero, zero_add] at h
    have h' : (w 2 : ℂ) * 1 + (w 3 : ℂ) * Complex.I = 0 := h
    have ere := congrArg Complex.re h'
    have eim := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
    norm_num at ere eim
    constructor <;> linarith
  have p311 : w 4 = 0 ∧ w 5 = 0 := by
    have h := hentry 3 11
    rw [sum_fin_ten, kv0_311, kv1_311, kv2_311, kv3_311, kv4_311, kv5_311, kv6_311, kv7_311, kv8_311, kv9_311] at h
    simp only [smul_zero, add_zero, zero_add] at h
    have h' : (w 4 : ℂ) * 1 + (w 5 : ℂ) * Complex.I = 0 := h
    have ere := congrArg Complex.re h'
    have eim := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
    norm_num at ere eim
    constructor <;> linarith
  have p925 : w 8 = 0 ∧ w 9 = 0 := by
    have h := hentry 9 25
    rw [sum_fin_ten, kv0_925, kv1_925, kv2_925, kv3_925, kv4_925, kv5_925, kv6_925, kv7_925, kv8_925, kv9_925] at h
    simp only [smul_zero, add_zero, zero_add] at h
    have h' : (w 8 : ℂ) * 1 + (w 9 : ℂ) * Complex.I = 0 := h
    have ere := congrArg Complex.re h'
    have eim := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
    norm_num at ere eim
    constructor <;> linarith
  have p08 : w 6 = 0 ∧ w 7 = 0 := by
    have h := hentry 0 8
    rw [sum_fin_ten, kv0_08, kv1_08, kv2_08, kv3_08, kv4_08, kv5_08, kv6_08, kv7_08, kv8_08, kv9_08] at h
    simp only [smul_zero, add_zero, zero_add] at h
    have h' : (w 6 : ℂ) * (((1/7 : ℝ) : ℂ) * 1) + (w 7 : ℂ) * (((1/7 : ℝ) : ℂ) * Complex.I) = 0 := h
    have ere := congrArg Complex.re h'
    have eim := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at ere eim
    norm_num at ere eim
    constructor <;> linarith
  intro i
  fin_cases i <;> [exact p19.1; exact p19.2; exact p210.1; exact p210.2; exact p311.1;
    exact p311.2; exact p08.1; exact p08.2; exact p925.1; exact p925.2]

/-- **P-VL1** (BR1-009, probe-landed 2026-10-30, re-confirmed 2026-11-01):
    the centralizer section of the seat `K0 = (smDirac 1 2 3 5 7)^2` over
    `W22` — the flux-zero sector of the seat, in the memo's language —
    has real dimension exactly `10`. -/
theorem P_VL1 : Module.finrank ℝ (LinearMap.ker (commMap K0)) = 10 := by
  rw [ker_eq_span, finrank_span_eq_card kvFin_independent, Fintype.card_fin]

end ThetLogos
