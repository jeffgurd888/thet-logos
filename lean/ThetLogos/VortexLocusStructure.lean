import ThetLogos.VortexLocusPin
import ThetLogos.ModularFlux

/-!
# Vortex-locus structure (VL-3): P-VL2 + P-VL3

Governing memo: `routeb-general-scratch/scoping-vortex-locus-2026-10-30.md`
(§1's P-VL2/P-VL3 and the VL-3 firing-order line; its §5 fences bind this
module's language).  VL-2 landed FULL in `VortexLocusPin.lean`: P-VL1
(`finrank ℝ (ker (commMap K0)) = 10`), `ker_eq_span` (the kernel is the
span of the ten registered directions `kvFin`), and the coordinate
read-back `dirs22Combo_mem_ker_iff`.  Everything below CITEs those
results; nothing of VL-2 is reproved or forked.  The probe data
(BR1-009, confirmed) governs the statement forms.

**Objects (memo §5).**  A commutator map, its kernel, a centralizer
section over `W22`.  The locus is the flux-ZERO sector: the silent
sector of the `W22` geometry at its own thermal `K`, not a flow result
and not a stability result in any dynamical sense.  The words "vortex",
"hydrodynamic" and "circulation" are Jeff's T5 vocabulary and appear
here only in the module name inherited from the pin; no statement below
asserts that a Yukawa block "is" a circulation flux.

**Seat (T2 chosen inputs, stated on the face).**  `K0 = (smDirac 1 2 3 5 7)^2`
with `y₀ = (yNu, yE, yU, yD, yR) = (1, 2, 3, 5, 7)`, `β = 1`, and the
`W22` direction span of `CFKernel22.lean`, exactly as in VL-2.

**What lands here.**

* **P-VL2 (structure / membership), FULL — and short, because VL-2's
  landed results make it a short assembly** (the pack's registered
  instruction: land it short and say so; no bulk is manufactured).
  The kernel is the real span of the explicit named sublist of the 22
  `dirs22` directions given by VL-2's basis `kvFin`: the six singles
  `dirs22 2, …, dirs22 7` (`smDirReE`, `smDirImE`, `smDirReU`,
  `smDirImU`, `smDirReD`, `smDirImD`), the two Nu/R combinations
  `(1/7) • dirs22 0 + dirs22 8` and `(1/7) • dirs22 1 + dirs22 9`
  (the relations `g 8 = 7 * g 0`, `g 9 = 7 * g 1`), and the two exotic
  singles `dirs22 20, dirs22 21` (`exoticReEREbarR`,
  `exoticImEREbarR`).  The free coordinates are `0–7, 20, 21`.
  Membership is settled direction by direction: the eight member
  singles and the two combinations are in the kernel (VL-2's theorems,
  repackaged in `P_VL2_members`); every other single named direction —
  `dirs22 0, 1, 8, 9` alone and `dirs22 10, …, dirs22 19` — is NOT in
  the kernel (`kvDir_not_mem_ker_*`), and the coordinate form
  (`P_VL2_no_others`) names the ten forced-zero coordinates
  `10, …, 19` and the two link relations, so there are no others.
  The `D_F(y₀)` line's membership is by CITATION of the landed
  `thermal_flux_vanishes` (§1): the forcing is cited, not reproved.

* **P-VL3 (family corollary), in the probe's TRUE form.**  The family
  locus `{y ∈ ℂ⁵ : [K₀, smDirac y] = 0}` is NOT the ℂ-line through `y₀`
  the scoping expected.  It is `(yE, yU, yD)` free (`ℂ³`) times the
  `(yNu, yR)` ℂ-line `yR = 7 * yNu` (§3: the iff, the set form, an
  explicit real parametrization by `Fin 8 → ℝ`, and real dimension
  exactly `8`).  The ℂ-line through `y₀` is contained in it
  (`family_line_through_y0_mem`, and at matrix level
  `df_complex_line_commutes`, by the same `thermal_flux_vanishes`
  citation).  The pre-named PARTIAL seam does not open: the family
  form closes from VL-2's landed §3 criterion
  (`comm_K0_buildDirac_diag`) plus one entry extraction
  (`comm_entry_0_8`, landed in VL-2), with no new computation layer.
  K-VORTEX-2 does NOT fire: the kernel strictly exceeds the forced
  `D_F(y₀)` line (dimension 10, not 1 — VL-2's P-VL1).

**NO CLAIM.**  Nothing here touches any Millennium statement; no dial
moves on any outcome.  The seat `(y₀, β = 1, W22)` is a T2 chosen input.

No `sorry`, no `native_decide`.
-/

namespace ThetLogos

open Matrix

/-! ## §1. The `D_F(y₀)` line, by citation of `thermal_flux_vanishes`

`thermal_flux_vanishes` (T1, `ModularFlux.lean`) states, for any `D`
and any real `β`, `modularFlux ((β : ℂ) • D ^ 2) D = 0`.  At `β = 1`
and `D = smDirac 1 2 3 5 7` this is `Complex.I • (K0 * D - D * K0) = 0`,
hence `K0 * D - D * K0 = 0` since `Complex.I ≠ 0`.  That citation —
not a reproof — is the forcing behind every membership statement in
this section. -/

/-- The seat Dirac operator commutes with `K0`, by citation of the
    landed `thermal_flux_vanishes` at `β = 1`. -/
theorem comm_K0_DF_zero :
    K0 * smDirac 1 2 3 5 7 - smDirac 1 2 3 5 7 * K0 = 0 := by
  have h := thermal_flux_vanishes (smDirac 1 2 3 5 7) (1 : ℝ)
  rw [modularFlux] at h
  simp only [Complex.ofReal_one, one_smul] at h
  rcases smul_eq_zero.mp h with hI | hsub
  · exfalso; exact Complex.I_ne_zero hI
  · exact hsub

/-- `D_F(y₀) = smDirac 1 2 3 5 7` as an element of `W22` (its
    admissibility is the landed `smDirac` admissibility package, in
    the same assembly as `smDirReNu_mem`). -/
def dfW : W22 := ⟨smDirac 1 2 3 5 7, by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 1 2 3 5 7
  · show smDirac 1 2 3 5 7 * cfMat - cfMat * smDirac 1 2 3 5 7 = 0
    exact smDirac_comm_cfMat 1 2 3 5 7
  · show (smDirac 1 2 3 5 7).conjTranspose = smDirac 1 2 3 5 7
    exact smDirac_self_adjoint 1 2 3 5 7
  · exact smDirac_IsJCompatible 1 2 3 5 7
  · show gammaF * smDirac 1 2 3 5 7 + smDirac 1 2 3 5 7 * gammaF = 0
    exact smDirac_grading_odd 1 2 3 5 7⟩

/-- The `D_F(y₀)` direction is a member of the kernel — the forced
    member, by the §1 citation. -/
theorem dfW_mem_ker : dfW ∈ LinearMap.ker (commMap K0) := by
  rw [LinearMap.mem_ker, commMap_apply]
  show K0 * dfW.val - dfW.val * K0 = 0
  exact comm_K0_DF_zero

/-- The whole real `D_F(y₀)` line lies in the kernel. -/
theorem df_real_line_mem_ker (t : ℝ) :
    t • dfW ∈ LinearMap.ker (commMap K0) :=
  Submodule.smul_mem _ t dfW_mem_ker

/-- The `D_F(y₀)` direction lies in the span of the ten registered
    kernel directions (via VL-2's `ker_eq_span`). -/
theorem dfW_mem_span :
    dfW ∈ Submodule.span ℝ (Set.range kvFin) := by
  rw [← ker_eq_span]
  exact dfW_mem_ker

/-- At matrix level, the whole complex line through `D_F(y₀)` commutes
    with `K0` — the scalar multiple of the §1 citation. -/
theorem df_complex_line_commutes (c : ℂ) :
    K0 * (c • smDirac 1 2 3 5 7) - (c • smDirac 1 2 3 5 7) * K0 = 0 := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, comm_K0_DF_zero, smul_zero]

/-! ## §2. P-VL2 — structure / membership, in the registered form

VL-2's `ker_eq_span` IS the span statement; P-VL2's content is the
registered packaging around it: the sublist in `dirs22` names, the
member list, the exclusion list, and the coordinate no-others form. -/

/-- **P-VL2 (span form).**  The kernel of `commMap K0` is the real span
    of VL-2's ten registered directions `kvFin`.  This is VL-2's landed
    `ker_eq_span`, cited as the headline of the structure brick. -/
theorem P_VL2 :
    LinearMap.ker (commMap K0) = Submodule.span ℝ (Set.range kvFin) :=
  ker_eq_span

/-- **P-VL2 (named-sublist form).**  The same span equality with the
    ten directions written out in `dirs22` names: the singles
    `dirs22 2, …, dirs22 7` (E/U/D real and imaginary), the two Nu/R
    combinations `(1/7) • dirs22 0 + dirs22 8` and
    `(1/7) • dirs22 1 + dirs22 9`, and the exotic singles
    `dirs22 20, dirs22 21`. -/
theorem P_VL2_named :
    LinearMap.ker (commMap K0) = Submodule.span ℝ (Set.range
      ![kvDir 2, kvDir 3, kvDir 4, kvDir 5, kvDir 6, kvDir 7,
        (1 / 7 : ℝ) • kvDir 0 + kvDir 8, (1 / 7 : ℝ) • kvDir 1 + kvDir 9,
        kvDir 20, kvDir 21]) :=
  ker_eq_span

/-- **P-VL2 (members).**  Every member of the named sublist lies in the
    kernel: the eight member singles and the two Nu/R combinations,
    each by VL-2's landed membership theorem. -/
theorem P_VL2_members :
    kvDir 2 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 3 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 4 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 5 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 6 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 7 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 20 ∈ LinearMap.ker (commMap K0) ∧
    kvDir 21 ∈ LinearMap.ker (commMap K0) ∧
    (1 / 7 : ℝ) • kvDir 0 + kvDir 8 ∈ LinearMap.ker (commMap K0) ∧
    (1 / 7 : ℝ) • kvDir 1 + kvDir 9 ∈ LinearMap.ker (commMap K0) :=
  ⟨kvDir_mem_ker_2, kvDir_mem_ker_3, kvDir_mem_ker_4, kvDir_mem_ker_5,
   kvDir_mem_ker_6, kvDir_mem_ker_7, kvDir_mem_ker_20, kvDir_mem_ker_21,
   kvCombo_re_mem_ker, kvCombo_im_mem_ker⟩

/-- **P-VL2 (no others, coordinate form).**  A coordinate vector in the
    kernel has its ten exotic coordinates `10, …, 19` forced to zero
    and its R coordinates linked by `g 8 = 7 * g 0`, `g 9 = 7 * g 1`;
    the free coordinates are exactly `0–7, 20, 21`.  This is the
    forward direction of VL-2's landed `dirs22Combo_mem_ker_iff`,
    repackaged in the registered order. -/
theorem P_VL2_no_others (g : Fin 22 → ℝ)
    (hg : dirs22Combo g ∈ LinearMap.ker (commMap K0)) :
    g 10 = 0 ∧ g 11 = 0 ∧ g 12 = 0 ∧ g 13 = 0 ∧ g 14 = 0 ∧ g 15 = 0 ∧
    g 16 = 0 ∧ g 17 = 0 ∧ g 18 = 0 ∧ g 19 = 0 ∧
    g 8 = 7 * g 0 ∧ g 9 = 7 * g 1 := by
  obtain ⟨h12, h13, h14, h15, h16, h17, h10, h11, h18, h19, h8, h9⟩ :=
    (dirs22Combo_mem_ker_iff g).mp hg
  exact ⟨h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h8, h9⟩

/-- A single named direction as a coordinate combination:
    `kvDir k = dirs22Combo (Pi.single k 1)`. -/
theorem kvDir_eq_single (k : Fin 22) :
    kvDir k = dirs22Combo (Pi.single k 1) := by
  apply Subtype.ext
  show dirs22 k = ∑ i, (Pi.single k (1 : ℝ) : Fin 22 → ℝ) i • dirs22 i
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · simp

/-- Exclusion: `dirs22 0` (`smDirReNu`) alone is not in the kernel
    (it enters only through the combination `(1/7) • dirs22 0 + dirs22 8`). -/
theorem kvDir_not_mem_ker_0 : kvDir 0 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 1` (`smDirImNu`) alone is not in the kernel. -/
theorem kvDir_not_mem_ker_1 : kvDir 1 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 8` (`smDirReR`) alone is not in the kernel
    (it enters only through the combination `(1/7) • dirs22 0 + dirs22 8`). -/
theorem kvDir_not_mem_ker_8 : kvDir 8 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 9` (`smDirImR`) alone is not in the kernel. -/
theorem kvDir_not_mem_ker_9 : kvDir 9 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 10` (`exoticReNuLeR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_10 : kvDir 10 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 11` (`exoticImNuLeR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_11 : kvDir 11 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 12` (`exoticReELNuR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_12 : kvDir 12 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 13` (`exoticImELNuR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_13 : kvDir 13 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 14` (`exoticReULDR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_14 : kvDir 14 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 15` (`exoticImULDR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_15 : kvDir 15 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 16` (`exoticReDLUR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_16 : kvDir 16 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 17` (`exoticImDLUR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_17 : kvDir 17 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 18` (`exoticReNuREbarR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_18 : kvDir 18 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-- Exclusion: `dirs22 19` (`exoticImNuREbarR`) is not in the kernel. -/
theorem kvDir_not_mem_ker_19 : kvDir 19 ∉ LinearMap.ker (commMap K0) := by
  intro h
  rw [kvDir_eq_single] at h
  have hc := (dirs22Combo_mem_ker_iff _).mp h
  simp at hc

/-! ## §3. P-VL3 — the family locus, in the probe's TRUE form

For a general parameter tuple `y = (yNu, yE, yU, yD, yR)`, the matrix
`smDirac y` is a diagonal-block `buildDirac` (VL-2's
`smDirac_eq_buildDirac_diag`) with Yukawa diagonal
`![yNu, yE, yU, yD, yU, yD, yU, yD]` and Majorana diagonal supported at
`a = 0` with value `yR`.  VL-2's §3 criterion
(`comm_K0_buildDirac_diag`) therefore gives commutation as soon as
`yR = 7 * yNu` — with `yE, yU, yD` wholly free.  Necessity is one
landed entry extraction: VL-2's `comm_entry_0_8` at the family matrix,
whose entries there are `yNu` (at `(0, 8)`), `yR` (at `(24, 8)`) and
`0` (at `(0, 16)`). -/

/-- The family matrix vanishes at `(0, 16)` (support disjointness,
    via the landed `smDirac_supp_aux`). -/
theorem smDirac_entry_0_16 (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR (0 : I32) (16 : I32) = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR (0 : I32) (16 : I32) h
  rcases hs with h1 | h1 | h1 | h1 | h1 | h1 <;> norm_num at h1

/-- The `(0, 8)` entry of the family commutator is `7 * (yR - 7 * yNu)`
    (from VL-2's landed extraction `comm_entry_0_8`). -/
theorem family_comm_entry_0_8 (yNu yE yU yD yR : ℂ) :
    (K0 * smDirac yNu yE yU yD yR - smDirac yNu yE yU yD yR * K0)
      (0 : I32) (8 : I32) = 7 * (yR - 7 * yNu) := by
  rw [comm_entry_0_8, smDirac_08, smDirac_24_8, smDirac_entry_0_16]
  ring

/-- **P-VL3 (iff form).**  A family member commutes with `K0` if and
    only if its `(yNu, yR)` coordinates lie on the ℂ-line
    `yR = 7 * yNu`; `yE, yU, yD` are unconstrained. -/
theorem P_VL3_iff (yNu yE yU yD yR : ℂ) :
    K0 * smDirac yNu yE yU yD yR - smDirac yNu yE yU yD yR * K0 = 0 ↔
      yR = 7 * yNu := by
  constructor
  · intro h
    have he := congrFun (congrFun h (0 : I32)) (8 : I32)
    rw [family_comm_entry_0_8] at he
    have h7 : (7 : ℂ) ≠ 0 := by norm_num
    have := mul_eq_zero.mp he
    rcases this with h0 | h0
    · exact absurd h0 h7
    · have : yR - 7 * yNu = 0 := h0
      exact eq_of_sub_eq_zero this
  · intro h
    have key := comm_K0_buildDirac_diag ![yNu, yE, yU, yD, yU, yD, yU, yD]
      (fun k : Fin 8 => if k.val = 0 then yR else 0) (by
        intro a ha
        have ha0 : a = 0 := Fin.ext ha
        subst ha0
        simp [h])
    rw [smDirac_eq_buildDirac_diag]
    exact key

/-- **P-VL3 (set form).**  The family locus, as a subset of `ℂ⁵`
    (coordinates `y 0 = yNu, y 1 = yE, y 2 = yU, y 3 = yD, y 4 = yR`),
    is exactly `{(yE, yU, yD) free} × {yR = 7 * yNu}`. -/
theorem P_VL3_set :
    {y : Fin 5 → ℂ | K0 * smDirac (y 0) (y 1) (y 2) (y 3) (y 4)
        - smDirac (y 0) (y 1) (y 2) (y 3) (y 4) * K0 = 0}
      = {y : Fin 5 → ℂ | y 4 = 7 * y 0} := by
  ext y
  exact P_VL3_iff (y 0) (y 1) (y 2) (y 3) (y 4)

/-- The explicit real parametrization of the family locus:
    eight real coordinates (real and imaginary parts of
    `yNu, yE, yU, yD`) mapping to
    `(yNu, yE, yU, yD, 7 * yNu)`. -/
def famParamR : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 5 → ℂ) where
  toFun t := ![(t 0 : ℂ) + Complex.I * (t 1 : ℂ),
               (t 2 : ℂ) + Complex.I * (t 3 : ℂ),
               (t 4 : ℂ) + Complex.I * (t 5 : ℂ),
               (t 6 : ℂ) + Complex.I * (t 7 : ℂ),
               7 * ((t 0 : ℂ) + Complex.I * (t 1 : ℂ))]
  map_add' t s := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' r t := by
    funext j
    fin_cases j <;> simp [smul_eq_mul] <;> ring

/-- The real parametrization is injective. -/
theorem famParamR_injective : Function.Injective famParamR := by
  intro t s h
  have h0 : (t 0 : ℂ) + Complex.I * (t 1 : ℂ)
      = (s 0 : ℂ) + Complex.I * (s 1 : ℂ) := by
    have := congrFun h 0
    simpa [famParamR] using this
  have h1 : (t 2 : ℂ) + Complex.I * (t 3 : ℂ)
      = (s 2 : ℂ) + Complex.I * (s 3 : ℂ) := by
    have := congrFun h 1
    simpa [famParamR] using this
  have h2 : (t 4 : ℂ) + Complex.I * (t 5 : ℂ)
      = (s 4 : ℂ) + Complex.I * (s 5 : ℂ) := by
    have := congrFun h 2
    simpa [famParamR] using this
  have h3 : (t 6 : ℂ) + Complex.I * (t 7 : ℂ)
      = (s 6 : ℂ) + Complex.I * (s 7 : ℂ) := by
    have := congrFun h 3
    simpa [famParamR] using this
  funext i
  fin_cases i
  · have := congrArg Complex.re h0
    simpa using this
  · have := congrArg Complex.im h0
    simpa using this
  · have := congrArg Complex.re h1
    simpa using this
  · have := congrArg Complex.im h1
    simpa using this
  · have := congrArg Complex.re h2
    simpa using this
  · have := congrArg Complex.im h2
    simpa using this
  · have := congrArg Complex.re h3
    simpa using this
  · have := congrArg Complex.im h3
    simpa using this

/-- The range of the real parametrization is exactly the family
    locus (as a set). -/
theorem famParamR_range_eq :
    (LinearMap.range famParamR : Set (Fin 5 → ℂ))
      = {y : Fin 5 → ℂ | K0 * smDirac (y 0) (y 1) (y 2) (y 3) (y 4)
          - smDirac (y 0) (y 1) (y 2) (y 3) (y 4) * K0 = 0} := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    show K0 * smDirac _ _ _ _ _ - smDirac _ _ _ _ _ * K0 = 0
    rw [P_VL3_iff]
    simp [famParamR]
  · intro hy
    have hcond : y 4 = 7 * y 0 := (P_VL3_iff (y 0) (y 1) (y 2) (y 3) (y 4)).mp hy
    refine ⟨![(y 0).re, (y 0).im, (y 1).re, (y 1).im, (y 2).re, (y 2).im,
              (y 3).re, (y 3).im], ?_⟩
    funext j
    fin_cases j
    · show (↑(y 0).re + Complex.I * ↑(y 0).im) = y 0
      rw [mul_comm Complex.I _, Complex.re_add_im]
    · show (↑(y 1).re + Complex.I * ↑(y 1).im) = y 1
      rw [mul_comm Complex.I _, Complex.re_add_im]
    · show (↑(y 2).re + Complex.I * ↑(y 2).im) = y 2
      rw [mul_comm Complex.I _, Complex.re_add_im]
    · show (↑(y 3).re + Complex.I * ↑(y 3).im) = y 3
      rw [mul_comm Complex.I _, Complex.re_add_im]
    · show 7 * (↑(y 0).re + Complex.I * ↑(y 0).im) = y 4
      rw [mul_comm Complex.I _, Complex.re_add_im, ← hcond]

/-- **P-VL3 (dimension).**  The family locus has real dimension
    exactly `8`: `(yE, yU, yD)` free in `ℂ³` (six real dimensions)
    times the `(yNu, yR)` ℂ-line `yR = 7 * yNu` (two real dimensions). -/
theorem P_VL3_finrank :
    Module.finrank ℝ (LinearMap.range famParamR) = 8 := by
  rw [LinearMap.finrank_range_of_inj famParamR_injective, Module.finrank_pi]
  simp

/-- The ℂ-line through `y₀` is contained in the family locus:
    every complex multiple of the parameter tuple `(1, 2, 3, 5, 7)`
    satisfies the family condition (its `(yNu, yR)` coordinates are
    `(c, 7c)`, on the line `yR = 7 * yNu`). -/
theorem family_line_through_y0_mem (c : ℂ) :
    K0 * smDirac (c * 1) (c * 2) (c * 3) (c * 5) (c * 7)
      - smDirac (c * 1) (c * 2) (c * 3) (c * 5) (c * 7) * K0 = 0 := by
  rw [P_VL3_iff]
  ring

/-- **P-VL3 (headline assembly).**  The family locus is the solution
    set of `yR = 7 * yNu` in `ℂ⁵` — `(yE, yU, yD)` free — and its real
    dimension is `8`. -/
theorem P_VL3 :
    ({y : Fin 5 → ℂ | K0 * smDirac (y 0) (y 1) (y 2) (y 3) (y 4)
        - smDirac (y 0) (y 1) (y 2) (y 3) (y 4) * K0 = 0}
      = {y : Fin 5 → ℂ | y 4 = 7 * y 0})
    ∧ Module.finrank ℝ (LinearMap.range famParamR) = 8
    ∧ (LinearMap.range famParamR : Set (Fin 5 → ℂ))
        = {y : Fin 5 → ℂ | K0 * smDirac (y 0) (y 1) (y 2) (y 3) (y 4)
            - smDirac (y 0) (y 1) (y 2) (y 3) (y 4) * K0 = 0} :=
  ⟨P_VL3_set, P_VL3_finrank, famParamR_range_eq⟩

end ThetLogos
