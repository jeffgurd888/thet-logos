/-
# R2 remainder (i) — the D₄ separation brick: discharging `d4KernelEqGap`

**R2 remainder (i)** (scoped 2026-11-08,
`r2-remainder-d4-separation-scope-2026-11-08.md`: BUILD, one
module, 20–35 strict, band M).  The D₄ miniature probe
(`LayerKernelPosD4Probe`) landed every field of the seat
certificate except one — the assembled kernel identity, named
there as `d4KernelEqGap` — and proved the reduction
`layerKernelPosD4Std_of_gaps`: the gap at every `β ≥ 0` closes
the pinned instance `layerKernelPosD4Std`.  This module is the
discharge.  Its design is the scoping's frozen shape §§A–E:
sign-character splitting (L4), the `nbRep` entry API (L5, L6,
L6′), the two-factor site averages by finite computation at
the seat (L9a–L9c, over the §2.2 channel basis), site
regrouping and assembly (L1–L3, L7, L8, L10), the separation
identity itself (SEP), and the headline (L12).

**BRICK 1 STAGING (2026-11-08).**  The lane's first write:
the module skeleton with every statement of the frozen shape
pinned at its scoping form, the assembly chain
`d4KernelEqGap_all` + `layerKernelPosD4Std_holds` proved from
the two named pins (`d4_separation`, `d4KernelEqGap_of_separation`),
and the remaining pins carried as `sorry` marked
`-- BRICK: TODO` (10 at that commit).

**BRICK 2 (2026-11-08).**  The seven finite lemmas of §§A–C
are proved: L4 (sign-character multiplicativity, by the
8-element case split), L6′ (entry reality), L6 (inverse
entries, via the landed `repMatrix_inv`), L5 (the trace
expansion), and L9a/L9c (the two-factor averages, by the
8-term sums — the helper `sum_dihedralGroup_four` unfolds
`∑ a : DihedralGroup 4` into its eight terms).  §D is opened:
the channel data of scoping §2.2 is pinned (`d4ChannelMat`,
the Pauli basis `E₁..E₄`; `D4Channel`, the per-site channel
index type) and the L7 site-regrouping identity is pinned as
a standalone statement.  Staging sorries at this commit:
**4** (§D ×2: `d4_separation`, `d4_site_regroup`; §E ×2:
`d4_layerAction_sum_columns`, `d4KernelEqGap_of_separation` —
see STATUS.md for the per-lemma ledger; the count is the
number of `sorry` proof bodies in this file at this commit,
restated in the commit message).  These headlines are **NOT
T1 yet**: they rest on the TODO pins, and `#print axioms`
shows `sorryAx` until brick 3 closes the pins.  The lane's
final deliverable is zero-sorry or a fired kill.

**BRICK 3 (2026-11-08) — FINAL STATE: PARTIAL.**  L7
(`d4_site_regroup`), L1 (`d4_layerAction_sum_columns`) and
the §E assembly (`d4KernelEqGap_of_separation`) are PROVED,
each on exactly `[propext, Classical.choice, Quot.sound]`;
the assembly is a conditional implication (separation data
in, the gap out), so it is sorry-free itself.  The L11
degeneracy check is PROVED (§F: the constant `sgnA` pattern
separates in closed form with a nonconstant explicit
feature, `d4_all_sgnA_stratum` + `d4_degeneracy_check`,
clean axioms) — **K-GRAM-DEGEN does not fire**.  The sole
remaining `sorry` in the module is `d4_separation` (SEP):
after L7 + L8 (landed), its proof reduces to the per-site
contraction of a word of up to six `a`-dependent factors
against the single site average, and the landed §C lemmas
contract at most two factors (L9a, L9c) or a character pair
(the sign filter).  The missing finite ingredient is the
pointwise isotypic (Clebsch–Gordan) expansion of the tensor
powers `M(a)^{⊗ m}`, `m ≤ 6`, with its channel constants
assembled into features — a sub-build of its own, priced
in STATUS.md at full rank.  Consequently `d4KernelEqGap_all`
and `layerKernelPosD4Std_holds` still carry `sorryAx` and
are **NOT T1**; K-LKP-MINI-D4 neither fires nor is
discharged (its target is exactly the gap SEP would close);
K-GRAM-SECTOR does not fire (its coefficient clause died at
the probe; the sector clause awaits the same contraction);
K-D4-SEP-COST does not fire (no computation blew the price:
the full module rebuild is ~25 s; the overrun is proof
size, not compute).  Module census at this commit: 32
theorems (31 proved, 1 sorry), 6 definitions, 38
declarations; exactly one `sorry` proof body in the file.

**BRICK 4 (2026-11-08) — FINAL STATE: SEP DISCHARGED.**
The pointwise Clebsch–Gordan expansion is built in §G
(54 theorems, 25 definitions/abbreviations): the channel
type of each §D channel matrix, the pointwise two-factor
expansion of entry pairs with channel constants
`(2:ℂ)⁻¹ • char`, the two-step site contraction separated
as a Klein-weighted coefficient times a `p`-side and a
`q`-side factor — equal on the nose (`Φ = Ψ`, by
`M⁻¹ = Mᵀ` and entry reality) — and the Gram assembly
`d4_stratum_gram` with features `√(weight) • Φ`.  No sign
obstruction occurs: odd standard-slot counts vanish
through the same formulas.  `d4_separation` is stated
after §G in the file (its proof consumes the §D basis and
the §E L7/L8 pins, which sit after its brick-1 site); the
frozen statement is byte-identical and the proof is
`d4_separation_proof`.  The module is zero-sorry and both
headlines print exactly `[propext, Classical.choice,
Quot.sound]` (audit at the file tail), so
`d4KernelEqGap_all` and `layerKernelPosD4Std_holds` are
T1: the D₄ standard instance closes at every `β ≥ 0`,
and remainder (i) is closed with it (remainder (ii),
general `d ≥ 2`, is untouched by this brick).
K-LKP-MINI-D4 does not fire (SEP is true at the seat);
K-GRAM-SECTOR does not fire (the Gram route landed);
K-D4-SEP-COST does not fire (compute stayed in band;
the overrun against the 20–35 price is proof size only —
a band deviation, disclosed: module census at this commit
is 86 theorems, 31 definitions/abbreviations, 117
declarations, zero `sorry` proof bodies).

Kills armed for the whole build (scoping §4):
**K-LKP-MINI-D4**, **K-GRAM-SECTOR**, **K-GRAM-DEGEN**
(its F3 test is L11, brick 3), and **K-D4-SEP-COST** (fires
iff the seat's finite computations blow the band-M price).
None fires in this brick.

**NO CLAIM.**  Parts of any official statement closed: 0.
**Dials 0/4; Dial 3 = 0** — even the finished brick lands one
finite instance; `LayerKernelPos` at general `(N, G, ρ)`,
`β > 0`, stays OPEN, and FACT stays dead (nothing here routes
through `StratumColumnFactorization`).
-/

import ThetLogos.LayerKernelPos
import ThetLogos.LayerKernelGramCert
import ThetLogos.LayerKernelGramCertOneDim
import ThetLogos.BlockingProjectionNonab
import ThetLogos.LayerKernelPosD4Probe

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

namespace ThetLogos

/-! ## §A. Sign characters (scoping L4)

For the four one-dimensional types, `d4Char τ` is a group
homomorphism `D₄ → ℂ` with values in `{±1}` — the first step
of OneDim's `prod_gramChar_colWord`, at this seat proved by
finite computation on the explicit characters (brick 2). -/

set_option linter.unusedSimpArgs false in
/-- **(L4)** The sign characters are multiplicative:
for `τ ∈ {triv, sgnA, sgnB, sgnC}`,
`d4Char τ (g * h) = d4Char τ g * d4Char τ h`.  Proved by the
finite check: case split on the 8 group elements for `g` and
`h`, the `DihedralGroup` multiplication table (the simp
lemmas `r_mul_r` etc.), and the 36 `ZMod 4` value facts
below — kernel `decide` is used only on `ZMod 4` / group
equalities, never on `ℂ`. -/
theorem d4Char_sign_mul (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (g h : DihedralGroup 4) :
    d4Char τ (g * h) = d4Char τ g * d4Char τ h := by
  -- The 36 `ZMod 4` value facts the finite check consumes:
  -- `(a ± b).val` and `a.val` for `a b ∈ {0, 1, 2, 3}`, each by
  -- kernel computation on the finite type (not on `ℂ`).
  have hv0 : (0 : ZMod 4).val = 0 := by decide
  have hv1 : (1 : ZMod 4).val = 1 := by decide
  have hv2 : (2 : ZMod 4).val = 2 := by decide
  have hv3 : (3 : ZMod 4).val = 3 := by decide
  have hs00 : ((0 + 0 : ZMod 4)).val = 0 := by decide
  have hd00 : ((0 - 0 : ZMod 4)).val = 0 := by decide
  have hs01 : ((0 + 1 : ZMod 4)).val = 1 := by decide
  have hd01 : ((0 - 1 : ZMod 4)).val = 3 := by decide
  have hs02 : ((0 + 2 : ZMod 4)).val = 2 := by decide
  have hd02 : ((0 - 2 : ZMod 4)).val = 2 := by decide
  have hs03 : ((0 + 3 : ZMod 4)).val = 3 := by decide
  have hd03 : ((0 - 3 : ZMod 4)).val = 1 := by decide
  have hs10 : ((1 + 0 : ZMod 4)).val = 1 := by decide
  have hd10 : ((1 - 0 : ZMod 4)).val = 1 := by decide
  have hs11 : ((1 + 1 : ZMod 4)).val = 2 := by decide
  have hd11 : ((1 - 1 : ZMod 4)).val = 0 := by decide
  have hs12 : ((1 + 2 : ZMod 4)).val = 3 := by decide
  have hd12 : ((1 - 2 : ZMod 4)).val = 3 := by decide
  have hs13 : ((1 + 3 : ZMod 4)).val = 0 := by decide
  have hd13 : ((1 - 3 : ZMod 4)).val = 2 := by decide
  have hs20 : ((2 + 0 : ZMod 4)).val = 2 := by decide
  have hd20 : ((2 - 0 : ZMod 4)).val = 2 := by decide
  have hs21 : ((2 + 1 : ZMod 4)).val = 3 := by decide
  have hd21 : ((2 - 1 : ZMod 4)).val = 1 := by decide
  have hs22 : ((2 + 2 : ZMod 4)).val = 0 := by decide
  have hd22 : ((2 - 2 : ZMod 4)).val = 0 := by decide
  have hs23 : ((2 + 3 : ZMod 4)).val = 1 := by decide
  have hd23 : ((2 - 3 : ZMod 4)).val = 3 := by decide
  have hs30 : ((3 + 0 : ZMod 4)).val = 3 := by decide
  have hd30 : ((3 - 0 : ZMod 4)).val = 3 := by decide
  have hs31 : ((3 + 1 : ZMod 4)).val = 0 := by decide
  have hd31 : ((3 - 1 : ZMod 4)).val = 2 := by decide
  have hs32 : ((3 + 2 : ZMod 4)).val = 1 := by decide
  have hd32 : ((3 - 2 : ZMod 4)).val = 1 := by decide
  have hs33 : ((3 + 3 : ZMod 4)).val = 2 := by decide
  have hd33 : ((3 - 3 : ZMod 4)).val = 0 := by decide
  have h8 : ∀ x : DihedralGroup 4, x = .r 0 ∨ x = .r 1 ∨ x = .r 2 ∨ x = .r 3
      ∨ x = .sr 0 ∨ x = .sr 1 ∨ x = .sr 2 ∨ x = .sr 3 := by decide
  rcases hτ with rfl | rfl | rfl | rfl
  · simp [d4Char]
  all_goals
    rcases h8 g with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h8 h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr, DihedralGroup.one_def, d4Char, d4SignChar,
      hv0, hv1, hv2, hv3, hs00, hs01, hs02, hs03, hs10, hs11, hs12, hs13,
      hs20, hs21, hs22, hs23, hs30, hs31, hs32, hs33, hd00, hd01, hd02, hd03,
      hd10, hd11, hd12, hd13, hd20, hd21, hd22, hd23, hd30, hd31, hd32, hd33,
      pow_succ, pow_zero] <;> ring

/-! ## §B. The `nbRep` entry API (scoping L5, L6, L6′)

`nbRep` lands in the unitary group, so inverse entries are
conjugate transposes (L6); every matrix in its image is a
signed permutation matrix, so entries are real (L6′) and
incoming-column factors are plain transposes.  L5 unfolds
`charFn nbRep` of a column word into the four-fold entry sum
that the site regrouping (L7) consumes. -/

/-- **(L6′)** Reality of the seat matrices:
`star (nbRepMat g i j) = nbRepMat g i j` — entries lie in
`{−1, 0, 1}`.  Finite check on the 8 elements: each matrix
is a power of `nbRot` (times `nbRefl` for the reflections),
and the `simp` evaluation of its entries closes on
`{−1, 0, 1}`-valued goals. -/
theorem nbRepMat_conj (g : DihedralGroup 4) (i j : Fin 2) :
    star (nbRepMat g i j) = nbRepMat g i j := by
  have h8 : ∀ x : DihedralGroup 4, x = .r 0 ∨ x = .r 1 ∨ x = .r 2 ∨ x = .r 3
      ∨ x = .sr 0 ∨ x = .sr 1 ∨ x = .sr 2 ∨ x = .sr 3 := by decide
  rcases h8 g with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp [nbRepMat, nbRotZ, nbRot, nbRefl, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, starRingEnd_apply,
      show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl, show ((-1 : ZMod 4)).val = 3 from rfl,
      show ((-2 : ZMod 4)).val = 2 from rfl, show ((-3 : ZMod 4)).val = 1 from rfl]

/-- **(L6)** Inverse entries are conjugate transposes: the
landed `repMatrix_inv` (the unitary-group API: the matrix
at `g⁻¹` is the conjugate transpose of the matrix at `g`)
at `nbRep`, read at the entry `(i, j)`. -/
theorem nbRepMat_inv_apply (g : DihedralGroup 4) (i j : Fin 2) :
    nbRepMat g⁻¹ i j = star (nbRepMat g j i) := by
  rw [← repMatrix_nbRep, repMatrix_inv, repMatrix_nbRep, Matrix.star_apply]

/-- **(L5)** Trace expansion of a column word:
`charFn nbRep` of the word is the four-fold sum of entry
products along the word `α c * u' ℓ * (α (σ c))⁻¹ * (u ℓ)⁻¹`.
The character is the trace of the matrix product
(`repMatrix_mul` splits the word's four factors — the two
inverse factors stay as matrices at inverse elements, as
the statement records), and `Matrix.trace` / `Matrix.mul_apply`
unfolding over `Fin 2` (`Fin.sum_univ_two`) leaves a finite
entry identity closed by `ring`. -/
theorem charFn_nbRep_colWord_expand
    (u u' : LayerLink 2 → DihedralGroup 4)
    (c : LayerSite 2) (ν : Fin 4) (hν : ν ≠ 0)
    (α : LayerSite 2 → DihedralGroup 4) :
    charFn nbRep (colWord u u' c ν hν α)
      = ∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ i₃ : Fin 2, ∑ i₄ : Fin 2,
          nbRepMat (α c) i₁ i₂
            * nbRepMat (u' (layerLinkOf c ν hν)) i₂ i₃
            * nbRepMat ((α (layerShift ν hν c))⁻¹) i₃ i₄
            * nbRepMat ((u (layerLinkOf c ν hν))⁻¹) i₄ i₁ := by
  show Matrix.trace (nbRepMat (α c * u' (layerLinkOf c ν hν)
      * (α (layerShift ν hν c))⁻¹ * (u (layerLinkOf c ν hν))⁻¹)) = _
  rw [← repMatrix_nbRep]
  simp only [repMatrix_mul, repMatrix_nbRep]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ## §C. The two-factor site averages (scoping L9a–L9c)

Matrix-coefficient orthogonality at this seat: each identity
is an 8-term sum of explicit integers (entries in `{−1, 0, 1}`,
sign characters in `{±1}`), discharged in brick 2 by finite
computation in the probe's idiom — no `native_decide`, no
kernel `decide` on `ℚ`/`ℂ`.  These are the seat instances of
the orthogonality formulas the pinned Mathlib does not state
(scoping §2.1). -/

/-- Sums over the seat group, unfolded: `∑ a : DihedralGroup 4`
is its eight terms.  The `univ` equality is by kernel
computation on the finite type; the expansion is the probe's
`Finset.sum_insert` idiom (`sum_D4Type`). -/
theorem sum_dihedralGroup_four {X : Type*} [AddCommMonoid X]
    (F : DihedralGroup 4 → X) :
    ∑ a, F a = F (.r 0) + F (.r 1) + F (.r 2) + F (.r 3)
      + F (.sr 0) + F (.sr 1) + F (.sr 2) + F (.sr 3) := by
  have h : (Finset.univ : Finset (DihedralGroup 4))
      = {.r 0, .r 1, .r 2, .r 3, .sr 0, .sr 1, .sr 2, .sr 3} := by decide
  rw [h]
  simp only [Finset.sum_insert (by decide : DihedralGroup.r 0
      ∉ ({.r 1, .r 2, .r 3, .sr 0, .sr 1, .sr 2, .sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_insert (by decide : DihedralGroup.r 1
      ∉ ({.r 2, .r 3, .sr 0, .sr 1, .sr 2, .sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_insert (by decide : DihedralGroup.r 2
      ∉ ({.r 3, .sr 0, .sr 1, .sr 2, .sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_insert (by decide : DihedralGroup.r 3
      ∉ ({.sr 0, .sr 1, .sr 2, .sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_insert (by decide : DihedralGroup.sr 0
      ∉ ({.sr 1, .sr 2, .sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_insert (by decide : DihedralGroup.sr 1
      ∉ ({.sr 2, .sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_insert (by decide : DihedralGroup.sr 2
      ∉ ({.sr 3} : Finset (DihedralGroup 4))),
    Finset.sum_singleton]
  simp only [← add_assoc]

/-- **(L9a)** Schur contraction: the averaged product of
two `std` matrix coefficients is the `(1/2) δ δ` contraction
of the two-dimensional unitary irrep.  Finite computation:
the eight terms of `sum_dihedralGroup_four`, entries of the
explicit matrices in `{−1, 0, 1}`, closed entry-wise over
the 16 index tuples. -/
theorem d4_schur_average (i j k l : Fin 2) :
    (8 : ℂ)⁻¹ * ∑ a : DihedralGroup 4,
        nbRepMat a i j * star (nbRepMat a k l)
      = (2 : ℂ)⁻¹ * (if i = k then 1 else 0)
          * (if j = l then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    rw [sum_dihedralGroup_four] <;>
    simp [nbRepMat, nbRotZ, nbRot, nbRefl, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, starRingEnd_apply,
      show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl, show ((-1 : ZMod 4)).val = 3 from rfl,
      show ((-2 : ZMod 4)).val = 2 from rfl, show ((-3 : ZMod 4)).val = 1 from rfl] <;>
    norm_num

/-- **(L9c)** Sign–`std` mixed averages vanish: `std`
carries no one-dimensional subrepresentation, so twisting its
coefficients by a sign character averages to `0`.  Finite
computation over the eight terms, as in L9a. -/
theorem d4_sign_std_average (τ : D4Type)
    (hτ : τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC) (i j : Fin 2) :
    (8 : ℂ)⁻¹ * ∑ a : DihedralGroup 4,
        d4Char τ a * nbRepMat a i j = 0 := by
  rcases hτ with rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    rw [sum_dihedralGroup_four] <;>
    simp [nbRepMat, nbRotZ, nbRot, nbRefl, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, starRingEnd_apply, d4Char, d4SignChar,
      show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl, show ((-1 : ZMod 4)).val = 3 from rfl,
      show ((-2 : ZMod 4)).val = 2 from rfl, show ((-3 : ZMod 4)).val = 1 from rfl] <;>
    norm_num

/-- **(L9c)** Sign-character orthonormality at the seat:
the four one-dimensional characters are orthonormal under the
group average.  Finite computation over the eight terms:
each character value is in `{±1}`, and the 16 type pairs are
checked entry-wise. -/
theorem d4_sign_orthonormal (τ τ' : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (hτ' : τ' = .triv ∨ τ' = .sgnA ∨ τ' = .sgnB ∨ τ' = .sgnC) :
    (8 : ℂ)⁻¹ * ∑ a : DihedralGroup 4,
        d4Char τ a * star (d4Char τ' a)
      = if τ = τ' then 1 else 0 := by
  rcases hτ with rfl | rfl | rfl | rfl <;>
    rcases hτ' with rfl | rfl | rfl | rfl <;>
    rw [sum_dihedralGroup_four] <;>
    simp [d4Char, d4SignChar,
      show (1 : ZMod 4).val = 1 from rfl, show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl] <;>
    norm_num

/-! ## §D. The separation identity (scoping SEP, L7–L10)

The heart of the build, pinned in sum form: for each fixed
type assignment `τof` to the 24 columns, the stratum sum of
the column-character product separates as a finite Gram sum.
The proof (bricks 2–3) expands `std` columns by L5, splits
sign columns by L4, regroups the 24-column product over the
8 sites (L7), factorizes the stratum sum over sites (L8,
proved below in §E), and contracts each site tensor
pairwise through §C. -/

/-- The separation property of one type assignment, in the
existential shape the gap itself uses: some finite channel
index set and feature family separate the stratum sum. -/
def D4Separated (τof : LayerColumn 2 → D4Type) : Prop :=
  ∃ (κ : Type) (hκ : Fintype κ)
    (feat : κ → (LayerLink 2 → DihedralGroup 4) → ℂ),
    ∀ u u' : LayerLink 2 → DihedralGroup 4,
      (∑ α : LayerSite 2 → DihedralGroup 4,
          ∏ P : LayerColumn 2,
            d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
        = ∑ k, feat k u * star (feat k u')

/-! **(SEP, PIN — relocated in brick 4)** `d4_separation`
is stated and proved below, after §E: its brick-4 proof
(§G: the pointwise Clebsch–Gordan expansion and the Gram
assembly) consumes the §D channel basis and the §E L7/L8
pins, which sit after this point in the file.  The frozen
statement is carried there byte-identical. -/

/-- The channel basis of `M₂(ℂ)` (scoping §2.2): the four
Pauli matrices `E₁ = 1`, `E₂ = nbRefl`, `E₃`, `E₄ = nbRot`,
pairwise Hilbert–Schmidt orthogonal, each of squared norm
`2`.  Under conjugation by `nbRep a` each `E_b` is carried
to a signed basis element — the concrete form of
`std ⊗ std ≅ triv ⊕ sgnA ⊕ sgnB ⊕ sgnC` at this seat, and of
the `std ⊗ std*` contraction
`δ_{ik} δ_{jl} = (1/2) ∑_b (E_b)_{ij} (E_b)_{lk}` whose
average form is L9a.  The orthogonality/completeness checks
are class-(a) finite computations, consumed in brick 3. -/
def d4ChannelMat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![1, 0; 0, -1]
  | 2 => !![0, 1; 1, 0]
  | 3 => !![0, -1; 1, 0]

/-- The channel index at a site (scoping §2.2, L12): one
`Fin 4` channel choice per pairwise contraction node of the
site tensor.  A site is the base of exactly 3 columns and
the shift-target of exactly 3, so three nodes suffice for
the pairwise-contraction tree brick 3 assembles; the joint
index of L12 is then
`(LayerColumn 2 → D4Type) × (LayerSite 2 → D4Channel)`.
Design point of brick 2, frozen as the pin's shape: if the
brick-3 contraction tree needs a flatter or larger node
list, this type is where the change lands — no other
statement names it yet. -/
def D4Channel : Type := Fin 4 × Fin 4 × Fin 4

/-- **(L7, PIN)** Site regrouping: a product over the 24
columns of (outgoing factor at the column's base site) ×
(incoming factor at the column's shift-target site) equals
the product over the 8 sites of (the outgoing factors based
at the site) × (the incoming factors shifted into the
site).  This is the factor-level regrouping the L9 site
factorization consumes once L4/L5 have split each column
factor into its outgoing and incoming parts
(`Finset.prod_fiberwise_of_maps_to` over the two column →
site maps).  Statement pinned at brick 2; the proof is
brick 3. -/
theorem d4_site_regroup (α : LayerSite 2 → DihedralGroup 4)
    (outF incF : LayerColumn 2 → DihedralGroup 4 → ℂ) :
    (∏ P : LayerColumn 2,
        outF P (α P.1) * incF P (α (layerShift P.2.1 P.2.2 P.1)))
      = ∏ c : LayerSite 2,
          (∏ P ∈ Finset.univ.filter (fun P : LayerColumn 2 => P.1 = c),
              outF P (α c))
            * ∏ P ∈ Finset.univ.filter
                (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1 = c),
                incF P (α c) := by
  have h1 : ∏ P : LayerColumn 2, outF P (α P.1)
      = ∏ c : LayerSite 2, ∏ P ∈ Finset.univ.filter
          (fun P : LayerColumn 2 => P.1 = c), outF P (α c) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ) (g := fun P : LayerColumn 2 => P.1)
      (f := fun P : LayerColumn 2 => outF P (α P.1))
      (fun P _ => Finset.mem_univ P.1)]
    refine Finset.prod_congr rfl fun c _ => ?_
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [(Finset.mem_filter.mp hP).2]
  have h2 : ∏ P : LayerColumn 2,
        incF P (α (layerShift P.2.1 P.2.2 P.1))
      = ∏ c : LayerSite 2, ∏ P ∈ Finset.univ.filter
          (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1 = c),
          incF P (α c) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ)
      (g := fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1)
      (f := fun P : LayerColumn 2 =>
        incF P (α (layerShift P.2.1 P.2.2 P.1)))
      (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun c _ => ?_
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [(Finset.mem_filter.mp hP).2]
  rw [Finset.prod_mul_distrib, h1, h2, ← Finset.prod_mul_distrib]

/-! ## §E. Assembly (scoping L1–L3, L8, L12)

L8 is the finite form of the product factorization OneDim's
`integral_gramPat` consumes in integral form; it is proved
here in brick 1.  L1 is pinned; the full assembly —
`layerKernel_d4_eq_sum` (landed), L1, the expansion insertion
(L2: `Real.exp_sum`, `Complex.ofReal_prod`, `Fintype.prod_sum`
over the landed `d4_expansion`), the weight extraction (L3),
and SEP — is brick 3's calc, mirroring OneDim's
`gram_kernel_eq` in sum form. -/

/-- **(L8)** Product factorization of the stratum sum:
a sum over site-assignments of a product of site-local
factors is the product of the per-site sums. -/
theorem d4_sum_prod_factor {F : LayerSite 2 → DihedralGroup 4 → ℂ} :
    (∑ α : LayerSite 2 → DihedralGroup 4, ∏ c, F c (α c))
      = ∏ c, ∑ a, F c a := by
  have h := Finset.sum_prod_piFinset (Finset.univ : Finset (DihedralGroup 4))
    (fun c a => F c a)
  rwa [Fintype.piFinset_univ] at h

/-- **(L1, PIN)** Action split: the negated one-layer action
is the column sum of `−β · gramDens` of the column words —
the `hreal` step of OneDim's `gram_kernel_eq`, re-instantiated
at the seat from the landed `layerAction_eq` /
`layerDensSum_eq_sum_columns` (brick 3). -/
theorem d4_layerAction_sum_columns (β : ℝ)
    (α : LayerSite 2 → DihedralGroup 4)
    (u u' : LayerLink 2 → DihedralGroup 4) :
    -(layerAction nbRep β α u u')
      = ∑ P : LayerColumn 2,
          (-β * gramDens nbRep (colWord u u' P.1 P.2.1 P.2.2 α)) := by
  rw [layerAction_eq, layerDensSum_eq_sum_columns nbRep (show Even 2 from ⟨1, rfl⟩),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hcd : colDensC nbRep u u' P α
      = gramDens nbRep (colWord u u' P.1 P.2.1 P.2.2 α) := rfl
  rw [hcd, neg_mul]

/-- At `N = 2` the layer shift is an involution (shifting by
`1` twice shifts by `2 = 0` in `ZMod 2`; the `y + y = 0` fact
is `decide` on the finite type `ZMod 2`). -/
theorem layerShift_two_involutive (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite 2) : layerShift ν hν (layerShift ν hν c) = c := by
  have h2 : ∀ y : ZMod 2, y + y = 0 := by decide
  apply Subtype.ext
  funext j
  show (torusShift 2 ν (torusShift 2 ν c.1)) j = c.1 j
  rw [torusShift_apply_coord, torusShift_apply_coord, ← add_assoc,
    h2, zero_add]

/-! ## §G. Brick 4 — the pointwise Clebsch–Gordan expansion
and the discharge of SEP

The brick-3 obstruction was the per-site contraction of a
word of up to six `a`-dependent factors: the landed §C
lemmas contract at most two factors, and only in averaged
form.  This section builds the pointwise expansion at the
seat instead.  Parts: (A) the channel type of each channel
matrix and the pointwise two-factor expansion of a product
`M(a) M(a')`-entry pair into channel components, with the
channel constants `(2:ℂ)⁻¹ • char`; (B) the averaged
corollaries recovering §C's averages pointwise; (C) the
two-step site contraction and its separation into a
Klein-weighted coefficient times a `p`-side and a `q`-side
factor, proved equal (`Φ = Ψ` on the nose, by `M⁻¹ = Mᵀ`
and entry reality); (D) the candidate-list form of the
site sum, the bracket identity against the landed L7/L8
regrouping, and the Gram assembly `d4_stratum_gram`: the
stratum sum is `∑ κ, feat κ u * star (feat κ u')` for the
explicit features `feat κ = √(weight κ) • Φ κ`.  No sign
obstruction occurs: odd standard-slot counts vanish
through the same formulas.  K-LKP-MINI-D4 does not fire. -/

/-- The one-dimensional channel type of the `b`-th channel
matrix: conjugation by `nbRep a` scales `d4ChannelMat b` by
`d4Char (d4TauChan b) a` (checked numerically and used through
the pointwise pair expansion below). -/
def d4TauChan : Fin 4 → D4Type
  | 0 => .triv
  | 1 => .sgnA
  | 2 => .sgnC
  | 3 => .sgnB

/-- Pointwise (Klein) product of one-dimensional types;
`std` is an absorbing junk value, never used at a sign type. -/
def d4Klein : D4Type → D4Type → D4Type
  | .triv, τ => τ
  | τ, .triv => τ
  | .sgnA, .sgnA => .triv
  | .sgnA, .sgnB => .sgnC
  | .sgnA, .sgnC => .sgnB
  | .sgnB, .sgnA => .sgnC
  | .sgnB, .sgnB => .triv
  | .sgnB, .sgnC => .sgnA
  | .sgnC, .sgnA => .sgnB
  | .sgnC, .sgnB => .sgnA
  | .sgnC, .sgnC => .triv
  | _, _ => .std

theorem d4Klein_sign {τ τ' : D4Type}
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (hτ' : τ' = .triv ∨ τ' = .sgnA ∨ τ' = .sgnB ∨ τ' = .sgnC) :
    d4Klein τ τ' = .triv ∨ d4Klein τ τ' = .sgnA
      ∨ d4Klein τ τ' = .sgnB ∨ d4Klein τ τ' = .sgnC := by
  rcases hτ with rfl | rfl | rfl | rfl <;>
    rcases hτ' with rfl | rfl | rfl | rfl <;> decide

/-- Sign characters take values in `{1, −1}` (finite check,
in the idiom of `d4Char_sgnA_mem`). -/
theorem d4Char_sign_mem (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (a : DihedralGroup 4) :
    d4Char τ a = 1 ∨ d4Char τ a = -1 := by
  have hv0 : (0 : ZMod 4).val = 0 := by decide
  have hv1 : (1 : ZMod 4).val = 1 := by decide
  have hv2 : (2 : ZMod 4).val = 2 := by decide
  have hv3 : (3 : ZMod 4).val = 3 := by decide
  have h8 : ∀ x : DihedralGroup 4, x = .r 0 ∨ x = .r 1 ∨ x = .r 2
      ∨ x = .r 3 ∨ x = .sr 0 ∨ x = .sr 1 ∨ x = .sr 2 ∨ x = .sr 3 := by
    decide
  rcases hτ with rfl | rfl | rfl | rfl <;>
    rcases h8 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [d4Char, d4SignChar, hv0, hv1, hv2, hv3] <;> norm_num

theorem d4Char_sign_one (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC) :
    d4Char τ 1 = 1 := by
  have h1 : (1 : DihedralGroup 4) = .r 0 := rfl
  rcases hτ with rfl | rfl | rfl | rfl <;> rw [h1] <;>
    simp [d4Char, d4SignChar]

theorem d4Char_sign_star (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (a : DihedralGroup 4) :
    star (d4Char τ a) = d4Char τ a := by
  rcases d4Char_sign_mem τ hτ a with h | h <;> simp [h]

/-- The character of an inverse equals the character, for
sign types (the values are `±1`, hence self-inverse). -/
theorem d4Char_sign_inv (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (a : DihedralGroup 4) :
    d4Char τ a⁻¹ = d4Char τ a := by
  have hmul : d4Char τ a⁻¹ * d4Char τ a = 1 := by
    have h := d4Char_sign_mul τ hτ a⁻¹ a
    rw [inv_mul_cancel, d4Char_sign_one τ hτ] at h
    exact h.symm
  rcases d4Char_sign_mem τ hτ a with h | h
  · have h2 : d4Char τ a⁻¹ = 1 := by
      rw [h, mul_one] at hmul
      exact hmul
    rw [h2, h]
  · have h2 : d4Char τ a⁻¹ = -1 := by
      rw [h] at hmul
      calc d4Char τ a⁻¹ = -(d4Char τ a⁻¹ * (-1 : ℂ)) := by ring
        _ = -1 := by rw [hmul]
    rw [h2, h]

/-- The Klein product of sign characters is the character of
the Klein product (finite check: 16 type pairs × 8 elements,
all concrete). -/
theorem d4Char_klein (τ τ' : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (hτ' : τ' = .triv ∨ τ' = .sgnA ∨ τ' = .sgnB ∨ τ' = .sgnC)
    (a : DihedralGroup 4) :
    d4Char (d4Klein τ τ') a = d4Char τ a * d4Char τ' a := by
  have hv0 : (0 : ZMod 4).val = 0 := by decide
  have hv1 : (1 : ZMod 4).val = 1 := by decide
  have hv2 : (2 : ZMod 4).val = 2 := by decide
  have hv3 : (3 : ZMod 4).val = 3 := by decide
  have h8 : ∀ x : DihedralGroup 4, x = .r 0 ∨ x = .r 1 ∨ x = .r 2
      ∨ x = .r 3 ∨ x = .sr 0 ∨ x = .sr 1 ∨ x = .sr 2 ∨ x = .sr 3 := by
    decide
  rcases hτ with rfl | rfl | rfl | rfl <;>
    rcases hτ' with rfl | rfl | rfl | rfl <;>
    rcases h8 a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [d4Klein, d4Char, d4SignChar, hv0, hv1, hv2, hv3] <;> norm_num

/-- The channel sign of every channel index is a
one-dimensional type. -/
theorem d4TauChan_sign (b : Fin 4) :
    d4TauChan b = .triv ∨ d4TauChan b = .sgnA
      ∨ d4TauChan b = .sgnB ∨ d4TauChan b = .sgnC := by
  fin_cases b <;> simp [d4TauChan]

/-- The pair expansion at rotations (finite check: 4 × 16
concrete instances). -/
theorem d4_pair_expand_r (i : ZMod 4) (p₁ q₁ p₂ q₂ : Fin 2) :
    nbRepMat (.r i) p₁ q₁ * nbRepMat (.r i) p₂ q₂
      = ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4Char (d4TauChan b) (.r i)
          * (d4ChannelMat b p₁ p₂ * d4ChannelMat b q₁ q₂) := by
  have hv : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hv i with rfl | rfl | rfl | rfl <;>
    fin_cases p₁ <;> fin_cases q₁ <;> fin_cases p₂ <;> fin_cases q₂ <;>
    rw [Fin.sum_univ_four] <;>
    simp [nbRepMat, nbRotZ, nbRot, nbRefl, d4TauChan, d4ChannelMat,
      d4Char, d4SignChar, Matrix.mul_apply, Fin.sum_univ_two, pow_succ,
      show (1 : ZMod 4).val = 1 from rfl,
      show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl] <;> norm_num

/-- The pair expansion at reflections (finite check: 4 × 16
concrete instances). -/
theorem d4_pair_expand_sr (i : ZMod 4) (p₁ q₁ p₂ q₂ : Fin 2) :
    nbRepMat (.sr i) p₁ q₁ * nbRepMat (.sr i) p₂ q₂
      = ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4Char (d4TauChan b) (.sr i)
          * (d4ChannelMat b p₁ p₂ * d4ChannelMat b q₁ q₂) := by
  have hv : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hv i with rfl | rfl | rfl | rfl <;>
    fin_cases p₁ <;> fin_cases q₁ <;> fin_cases p₂ <;> fin_cases q₂ <;>
    rw [Fin.sum_univ_four] <;>
    simp [nbRepMat, nbRotZ, nbRot, nbRefl, d4TauChan, d4ChannelMat,
      d4Char, d4SignChar, Matrix.mul_apply, Fin.sum_univ_two, pow_succ,
      show (1 : ZMod 4).val = 1 from rfl,
      show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl,
      show ((-1 : ZMod 4)).val = 3 from rfl,
      show ((-2 : ZMod 4)).val = 2 from rfl,
      show ((-3 : ZMod 4)).val = 1 from rfl] <;> norm_num

/-- **(R3, pointwise pair expansion)** The pointwise
Clebsch–Gordan identity at the seat: a product of two `std`
entries is the channel sum of `E_b`-contractions with
coefficients `(1/2) · χ_{τ(b)}(a)`. -/
theorem d4_pair_expand (a : DihedralGroup 4) (p₁ q₁ p₂ q₂ : Fin 2) :
    nbRepMat a p₁ q₁ * nbRepMat a p₂ q₂
      = ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4Char (d4TauChan b) a
          * (d4ChannelMat b p₁ p₂ * d4ChannelMat b q₁ q₂) := by
  cases a with
  | r i => exact d4_pair_expand_r i p₁ q₁ p₂ q₂
  | sr i => exact d4_pair_expand_sr i p₁ q₁ p₂ q₂

/-- The untwisted `std` average vanishes (the `triv` case of
the site recursion's odd-word vanishing). -/
theorem d4_std_average (p q : Fin 2) :
    ∑ a : DihedralGroup 4, nbRepMat a p q = 0 := by
  fin_cases p <;> fin_cases q <;> rw [sum_dihedralGroup_four] <;>
    simp [nbRepMat, nbRotZ, nbRot, nbRefl, Matrix.mul_apply,
      Fin.sum_univ_two, pow_succ, starRingEnd_apply,
      show (1 : ZMod 4).val = 1 from rfl,
      show (2 : ZMod 4).val = 2 from rfl,
      show (3 : ZMod 4).val = 3 from rfl,
      show ((-1 : ZMod 4)).val = 3 from rfl,
      show ((-2 : ZMod 4)).val = 2 from rfl,
      show ((-3 : ZMod 4)).val = 1 from rfl] <;> norm_num

/-- Every one-dimensional twist of a single `std` entry
averages to zero (signs by L9c; `triv` by `d4_std_average`). -/
theorem d4_char_std_average (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (p q : Fin 2) :
    ∑ a : DihedralGroup 4, d4Char τ a * nbRepMat a p q = 0 := by
  rcases hτ with rfl | rfl | rfl | rfl
  · simpa [d4Char] using d4_std_average p q
  · have h := d4_sign_std_average .sgnA (Or.inl rfl) p q
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  · have h := d4_sign_std_average .sgnB (Or.inr (Or.inl rfl)) p q
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  · have h := d4_sign_std_average .sgnC (Or.inr (Or.inr rfl)) p q
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'

/-- The character sum over the group: `8` at `triv`, else
`0` (from `d4_sign_orthonormal` against `triv`). -/
theorem d4_char_sum (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC) :
    (∑ a : DihedralGroup 4, d4Char τ a)
      = if τ = .triv then 8 else 0 := by
  have htriv : ∀ a : DihedralGroup 4, d4Char .triv a = 1 :=
    fun a => rfl
  have h := d4_sign_orthonormal τ .triv hτ (Or.inl rfl)
  simp only [htriv, star_one, mul_one] at h
  by_cases hτt : τ = .triv
  · rw [if_pos hτt] at h ⊢
    have h2 := congrArg (fun z : ℂ => (8 : ℂ) * z) h
    simpa using h2
  · rw [if_neg hτt] at h ⊢
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'

/-- **The site contraction**: the value of the site sum
`∑ a, χ_τ(a) · ∏ (entries)` over a list of end-pairs,
computed by the pointwise Clebsch–Gordan recursion (R3):
peel the first two entries, contract them through the
channel basis, and recurse with the Klein-twisted sign.
An odd leftover entry contracts to `0` (the twisted averages
vanish); the empty word leaves the character sum. -/
noncomputable def d4SiteContract : D4Type → List (Fin 2 × Fin 2) → ℂ
  | τ, [] => if τ = .triv then 8 else 0
  | _, [_] => 0
  | τ, x :: y :: rest =>
      ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4ChannelMat b x.1 y.1
        * d4ChannelMat b x.2 y.2
        * d4SiteContract (d4Klein τ (d4TauChan b)) rest

-- equation tests
example (τ : D4Type) : d4SiteContract τ [] = if τ = .triv then 8 else 0 := rfl
example (τ : D4Type) (x : Fin 2 × Fin 2) : d4SiteContract τ [x] = 0 := rfl
example (τ : D4Type) (x y : Fin 2 × Fin 2) (rest : List (Fin 2 × Fin 2)) :
    d4SiteContract τ (x :: y :: rest)
      = ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4ChannelMat b x.1 y.1
          * d4ChannelMat b x.2 y.2
          * d4SiteContract (d4Klein τ (d4TauChan b)) rest := rfl

/-- **(Site lemma)** The site sum over a word of `std`
entries twisted by a sign character equals the site
contraction.  Strong induction on the word length: the
empty word is the character sum (`d4_char_sum`), a single
entry is a vanishing twisted average (`d4_char_std_average`),
and a pair is contracted pointwise by R3, leaving the
Klein-twisted recursion. -/
theorem d4_site_sum_contract (τ : D4Type)
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (L : List (Fin 2 × Fin 2)) :
    (∑ a : DihedralGroup 4,
        d4Char τ a * (L.map (fun p => nbRepMat a p.1 p.2)).prod)
      = d4SiteContract τ L := by
  -- Two-step induction: prove `P L ∧ ∀ x, P (x :: L)` by list
  -- induction (the recursion twists `τ`, so `τ` is universally
  -- quantified inside `P`).
  have key : ∀ (L : List (Fin 2 × Fin 2)),
      (∀ (τ : D4Type),
        (τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC) →
        (∑ a : DihedralGroup 4,
            d4Char τ a * (L.map (fun p => nbRepMat a p.1 p.2)).prod)
          = d4SiteContract τ L)
      ∧ (∀ (τ : D4Type) (x : Fin 2 × Fin 2),
          (τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC) →
          (∑ a : DihedralGroup 4,
              d4Char τ a
                * ((x :: L).map (fun p => nbRepMat a p.1 p.2)).prod)
            = d4SiteContract τ (x :: L)) := by
    intro L
    induction L with
    | nil =>
      constructor
      · intro τ hτ
        simp only [List.map_nil, List.prod_nil, mul_one]
        rw [d4_char_sum τ hτ]
        rfl
      · intro τ x hτ
        simp only [List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one]
        exact d4_char_std_average τ hτ x.1 x.2
    | cons x L ih =>
      refine ⟨fun τ hτ => ih.2 τ x hτ, fun τ y hτ => ?_⟩
      -- The pair step: contract the first two entries of
      -- `y :: x :: L` by R3 and recurse on `L` (via `ih.1`).
      have hprod : ∀ a : DihedralGroup 4,
          ((y :: x :: L).map (fun p => nbRepMat a p.1 p.2)).prod
            = nbRepMat a y.1 y.2 * (nbRepMat a x.1 x.2
                * (L.map (fun p => nbRepMat a p.1 p.2)).prod) := by
        intro a
        simp [List.map_cons, List.prod_cons]
      simp only [hprod]
      calc (∑ a : DihedralGroup 4, d4Char τ a
              * (nbRepMat a y.1 y.2 * (nbRepMat a x.1 x.2
                  * (L.map (fun p => nbRepMat a p.1 p.2)).prod)))
          = ∑ a : DihedralGroup 4, d4Char τ a
              * ((nbRepMat a y.1 y.2 * nbRepMat a x.1 x.2)
                  * (L.map (fun p => nbRepMat a p.1 p.2)).prod) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [mul_assoc (nbRepMat a y.1 y.2) (nbRepMat a x.1 x.2)]
        _ = ∑ a : DihedralGroup 4, d4Char τ a
              * ((∑ b : Fin 4, (2 : ℂ)⁻¹ * d4Char (d4TauChan b) a
                    * (d4ChannelMat b y.1 x.1 * d4ChannelMat b y.2 x.2))
                  * (L.map (fun p => nbRepMat a p.1 p.2)).prod) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [d4_pair_expand a y.1 y.2 x.1 x.2]
        _ = ∑ a : DihedralGroup 4, ∑ b : Fin 4, d4Char τ a
              * (((2 : ℂ)⁻¹ * d4Char (d4TauChan b) a
                    * (d4ChannelMat b y.1 x.1 * d4ChannelMat b y.2 x.2))
                  * (L.map (fun p => nbRepMat a p.1 p.2)).prod) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ b : Fin 4, ∑ a : DihedralGroup 4, d4Char τ a
              * (((2 : ℂ)⁻¹ * d4Char (d4TauChan b) a
                    * (d4ChannelMat b y.1 x.1 * d4ChannelMat b y.2 x.2))
                  * (L.map (fun p => nbRepMat a p.1 p.2)).prod) :=
            Finset.sum_comm
        _ = ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4ChannelMat b y.1 x.1
              * d4ChannelMat b y.2 x.2
              * (∑ a : DihedralGroup 4,
                  d4Char (d4Klein τ (d4TauChan b)) a
                    * (L.map (fun p => nbRepMat a p.1 p.2)).prod) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            have e1 : d4Char τ a
                  * (((2 : ℂ)⁻¹ * d4Char (d4TauChan b) a
                      * (d4ChannelMat b y.1 x.1 * d4ChannelMat b y.2 x.2))
                    * (L.map (fun p => nbRepMat a p.1 p.2)).prod)
                = ((2 : ℂ)⁻¹ * (d4Char τ a * d4Char (d4TauChan b) a))
                    * (d4ChannelMat b y.1 x.1 * d4ChannelMat b y.2 x.2)
                    * (L.map (fun p => nbRepMat a p.1 p.2)).prod := by
              ring
            rw [e1, ← d4Char_klein τ (d4TauChan b) hτ (d4TauChan_sign b) a]
            ring
        _ = ∑ b : Fin 4, (2 : ℂ)⁻¹ * d4ChannelMat b y.1 x.1
              * d4ChannelMat b y.2 x.2
              * d4SiteContract (d4Klein τ (d4TauChan b)) L := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [ih.1 (d4Klein τ (d4TauChan b))
              (d4Klein_sign hτ (d4TauChan_sign b))]
        _ = d4SiteContract τ (y :: x :: L) := rfl
  exact (key L).1 τ hτ

/-- The row-end factor of a separated site contraction: the
product of the channel matrices at the pairs' row ends.
Mismatched lengths (an odd leftover, or channels left over)
give `0`; the exact-length diagonal gives the product. -/
def d4SitePF : List (Fin 4) → List (Fin 2 × Fin 2) → ℂ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | b :: bs, x :: y :: rest => d4ChannelMat b x.1 y.1 * d4SitePF bs rest
  | _ :: _, [_] => 0

/-- The column-end factor of a separated site contraction
(the `d4SitePF` shape at the pairs' column ends). -/
def d4SiteQF : List (Fin 4) → List (Fin 2 × Fin 2) → ℂ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | b :: bs, x :: y :: rest => d4ChannelMat b x.2 y.2 * d4SiteQF bs rest
  | _ :: _, [_] => 0

/-- The scalar coefficient of a separated site contraction:
`(1/2)` per contraction node, times the character filter
`8` when the accumulated Klein twist is trivial (as a
nonnegative real, cast to `ℂ`). -/
noncomputable def d4SiteCoeff (τ : D4Type) (bs : List (Fin 4)) : ℂ :=
  (((1 / 2 : ℝ) ^ bs.length
    * (if bs.foldl (fun acc b => d4Klein acc (d4TauChan b)) τ = .triv
        then 8 else 0) : ℝ) : ℂ)

-- equation tests for PF/QF
example (b : Fin 4) (bs : List (Fin 4)) (x y : Fin 2 × Fin 2)
    (rest : List (Fin 2 × Fin 2)) :
    d4SitePF (b :: bs) (x :: y :: rest)
      = d4ChannelMat b x.1 y.1 * d4SitePF bs rest := rfl
example (b : Fin 4) (bs : List (Fin 4)) (x y : Fin 2 × Fin 2)
    (rest : List (Fin 2 × Fin 2)) :
    d4SiteQF (b :: bs) (x :: y :: rest)
      = d4ChannelMat b x.2 y.2 * d4SiteQF bs rest := rfl
example : d4SitePF [] [] = 1 := rfl
example (x : Fin 2 × Fin 2) : d4SitePF [] [x] = 0 := rfl

/-- The coefficient recursion: one more channel costs a
factor `(2)⁻¹` and Klein-twists the accumulator. -/
theorem d4SiteCoeff_cons (τ : D4Type) (b : Fin 4)
    (bs : List (Fin 4)) :
    d4SiteCoeff τ (b :: bs)
      = (2 : ℂ)⁻¹ * d4SiteCoeff (d4Klein τ (d4TauChan b)) bs := by
  rw [d4SiteCoeff, d4SiteCoeff, List.length_cons, pow_succ,
    List.foldl_cons]
  push_cast
  ring

/-- Head/tail equivalence for channel assignments. -/
def d4ConsEquiv (n : ℕ) : (Fin (n + 1) → Fin 4) ≃ Fin 4 × (Fin n → Fin 4) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    obtain ⟨b, f⟩ := p
    apply Prod.ext
    · exact Fin.cons_zero (α := fun _ => Fin 4) b f
    · funext i
      exact Fin.cons_succ (α := fun _ => Fin 4) b f i

/-- Splitting a channel-assignment sum by its head. -/
theorem d4_sum_ofFn_succ (n : ℕ) (F : List (Fin 4) → ℂ) :
    (∑ bs : Fin (n + 1) → Fin 4, F (List.ofFn bs))
      = ∑ b : Fin 4, ∑ bs' : Fin n → Fin 4, F (b :: List.ofFn bs') := by
  calc (∑ bs : Fin (n + 1) → Fin 4, F (List.ofFn bs))
      = ∑ p : Fin 4 × (Fin n → Fin 4), F (p.1 :: List.ofFn p.2) := by
        refine Fintype.sum_equiv (d4ConsEquiv n) _ _ fun bs => ?_
        show F (List.ofFn bs) = F (bs 0 :: List.ofFn (Fin.tail bs))
        conv_lhs => rw [← Fin.cons_self_tail bs, List.ofFn_cons]
    _ = ∑ b : Fin 4, ∑ bs' : Fin n → Fin 4, F (b :: List.ofFn bs') :=
        Fintype.sum_prod_type _

/-- The sum over the empty channel assignment type. -/
theorem d4_sum_ofFn_zero (F : List (Fin 4) → ℂ) :
    (∑ bs : Fin 0 → Fin 4, F (List.ofFn bs)) = F [] := by
  have h : ∀ bs : Fin 0 → Fin 4, List.ofFn bs = [] := by
    intro bs
    cases h3 : List.ofFn bs with
    | nil => rfl
    | cons a t =>
      have hlen := List.length_ofFn (f := bs)
      rw [h3] at hlen
      simp at hlen
  rw [Finset.sum_congr rfl (fun bs _ => by rw [h bs])]
  exact Fintype.sum_unique _

/-- **(Separation of the site contraction)** The site
contraction is a finite sum over channel assignments of
coefficient × row-factor × column-factor.  Two-step
induction on the word, through `d4_sum_ofFn_succ`. -/
theorem d4_siteContract_sep (τ : D4Type) (L : List (Fin 2 × Fin 2)) :
    d4SiteContract τ L
      = ∑ bs : Fin (L.length / 2) → Fin 4,
          d4SiteCoeff τ (List.ofFn bs) * d4SitePF (List.ofFn bs) L
            * d4SiteQF (List.ofFn bs) L := by
  have key : ∀ (L : List (Fin 2 × Fin 2)),
      (∀ (τ : D4Type), d4SiteContract τ L
        = ∑ bs : Fin (L.length / 2) → Fin 4,
            d4SiteCoeff τ (List.ofFn bs) * d4SitePF (List.ofFn bs) L
              * d4SiteQF (List.ofFn bs) L)
      ∧ (∀ (τ : D4Type) (x : Fin 2 × Fin 2), d4SiteContract τ (x :: L)
        = ∑ bs : Fin ((x :: L).length / 2) → Fin 4,
            d4SiteCoeff τ (List.ofFn bs)
              * d4SitePF (List.ofFn bs) (x :: L)
              * d4SiteQF (List.ofFn bs) (x :: L)) := by
    intro L
    induction L with
    | nil =>
      constructor
      · intro τ
        show d4SiteContract τ [] = ∑ bs : Fin 0 → Fin 4,
          d4SiteCoeff τ (List.ofFn bs) * d4SitePF (List.ofFn bs) []
            * d4SiteQF (List.ofFn bs) []
        rw [d4_sum_ofFn_zero (fun l => d4SiteCoeff τ l * d4SitePF l []
          * d4SiteQF l [])]
        have hPF : d4SitePF [] [] = (1 : ℂ) := rfl
        have hQF : d4SiteQF [] [] = (1 : ℂ) := rfl
        by_cases h : τ = .triv
        · subst h
          show (8 : ℂ) = d4SiteCoeff .triv [] * d4SitePF [] []
            * d4SiteQF [] []
          rw [hPF, hQF, d4SiteCoeff]
          norm_num
        · show (if τ = .triv then (8 : ℂ) else 0)
            = d4SiteCoeff τ [] * d4SitePF [] [] * d4SiteQF [] []
          rw [if_neg h, hPF, hQF]
          simp [d4SiteCoeff, h]
      · intro τ x
        rw [show (x :: []).length / 2 = 0 from by simp]
        show d4SiteContract τ [x] = ∑ bs : Fin 0 → Fin 4,
          d4SiteCoeff τ (List.ofFn bs) * d4SitePF (List.ofFn bs) [x]
            * d4SiteQF (List.ofFn bs) [x]
        rw [d4_sum_ofFn_zero (fun l => d4SiteCoeff τ l * d4SitePF l [x]
          * d4SiteQF l [x])]
        show (0 : ℂ) = d4SiteCoeff τ [] * d4SitePF [] [x]
          * d4SiteQF [] [x]
        rw [show d4SitePF [] [x] = (0 : ℂ) from rfl]
        simp
    | cons x L ih =>
      refine ⟨fun τ => ih.2 τ x, fun τ y => ?_⟩
      have hlen : (y :: x :: L).length / 2 = L.length / 2 + 1 := by
        have h2 : (y :: x :: L).length = L.length + 2 := rfl
        omega
      rw [hlen, d4_sum_ofFn_succ (L.length / 2)
        (fun l => d4SiteCoeff τ l * d4SitePF l (y :: x :: L)
          * d4SiteQF l (y :: x :: L))]
      show (∑ b : Fin 4, (2 : ℂ)⁻¹ * d4ChannelMat b y.1 x.1
          * d4ChannelMat b y.2 x.2
          * d4SiteContract (d4Klein τ (d4TauChan b)) L) = _
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ih.1 (d4Klein τ (d4TauChan b)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun bs' _ => ?_
      rw [d4SiteCoeff_cons]
      show (2 : ℂ)⁻¹ * d4ChannelMat b y.1 x.1 * d4ChannelMat b y.2 x.2
          * (d4SiteCoeff (d4Klein τ (d4TauChan b)) (List.ofFn bs')
            * d4SitePF (List.ofFn bs') L * d4SiteQF (List.ofFn bs') L)
        = ((2 : ℂ)⁻¹
            * d4SiteCoeff (d4Klein τ (d4TauChan b)) (List.ofFn bs'))
          * (d4ChannelMat b y.1 x.1 * d4SitePF (List.ofFn bs') L)
          * (d4ChannelMat b y.2 x.2 * d4SiteQF (List.ofFn bs') L)
      ring
  exact (key L).1 τ

/-- A type different from `std` is one-dimensional. -/
theorem d4Type_sign_of_ne_std {τ : D4Type} (h : τ ≠ .std) :
    τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC := by
  cases τ <;> simp_all

/-- The `std` columns of a pattern, as a subtype. -/
abbrev D4StdCol (τof : LayerColumn 2 → D4Type) :=
  {P : LayerColumn 2 // τof P = .std}

/-- The slots of a pattern: a `std` column and a side
(`0` = outgoing at the base site, `1` = incoming at the
shift-target site). -/
abbrev D4Slot (τof : LayerColumn 2 → D4Type) := D4StdCol τof × Fin 2

example (τof : LayerColumn 2 → D4Type) : Fintype (D4StdCol τof) :=
  inferInstance
example (τof : LayerColumn 2 → D4Type) : Fintype (D4Slot τof) :=
  inferInstance

/-- The candidate columns at a site, in the frozen order:
the three outgoing columns `(c, ν)` and the three incoming
columns `(σ_ν c, ν)`, `ν ∈ {1, 2, 3}`, each tagged with its
side (`0` = outgoing, `1` = incoming). -/
def d4CandList (c : LayerSite 2) : List (LayerColumn 2 × Fin 2) :=
  [(⟨c, ⟨1, by decide⟩⟩, 0), (⟨c, ⟨2, by decide⟩⟩, 0),
   (⟨c, ⟨3, by decide⟩⟩, 0),
   (⟨layerShift 1 (by decide) c, ⟨1, by decide⟩⟩, 1),
   (⟨layerShift 2 (by decide) c, ⟨2, by decide⟩⟩, 1),
   (⟨layerShift 3 (by decide) c, ⟨3, by decide⟩⟩, 1)]

/-- The `a`-dependent factor of one candidate at a site:
for a `std` column, the `nbRep` entry at the slot's ends;
for a sign column, its character. -/
noncomputable def d4CandFactor (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (a : DihedralGroup 4) :
    LayerColumn 2 × Fin 2 → ℂ
  | (P, s) => if h : τof P = .std then
      nbRepMat a (e ⟨⟨P, h⟩, s⟩).1 (e ⟨⟨P, h⟩, s⟩).2
    else d4Char (τof P) a

/-- The accumulated sign type of a candidate list: the
Klein product of the sign columns' types. -/
def d4CandKlein (τof : LayerColumn 2 → D4Type) :
    List (LayerColumn 2 × Fin 2) → D4Type
  | [] => .triv
  | (P, _) :: rest => if τof P = .std then d4CandKlein τof rest
      else d4Klein (τof P) (d4CandKlein τof rest)

theorem d4CandKlein_sign (τof : LayerColumn 2 → D4Type)
    (cands : List (LayerColumn 2 × Fin 2)) :
    d4CandKlein τof cands = .triv ∨ d4CandKlein τof cands = .sgnA
      ∨ d4CandKlein τof cands = .sgnB
      ∨ d4CandKlein τof cands = .sgnC := by
  induction cands with
  | nil => exact Or.inl rfl
  | cons hd rest ih =>
    obtain ⟨P, s⟩ := hd
    by_cases h : τof P = .std
    · have hklein : d4CandKlein τof ((P, s) :: rest)
          = d4CandKlein τof rest := by
        show (if τof P = .std then d4CandKlein τof rest else _) = _
        rw [if_pos h]
      rw [hklein]
      exact ih
    · have hklein : d4CandKlein τof ((P, s) :: rest)
          = d4Klein (τof P) (d4CandKlein τof rest) := by
        show (if τof P = .std then _
          else d4Klein (τof P) (d4CandKlein τof rest)) = _
        rw [if_neg h]
      rw [hklein]
      exact d4Klein_sign (d4Type_sign_of_ne_std h) ih

/-- The `std` slots of a candidate list, in order. -/
def d4CandSlots (τof : LayerColumn 2 → D4Type) :
    List (LayerColumn 2 × Fin 2) → List (D4Slot τof)
  | [] => []
  | (P, s) :: rest => if h : τof P = .std
      then ⟨⟨P, h⟩, s⟩ :: d4CandSlots τof rest
      else d4CandSlots τof rest

/-- The end-pairs of the `std` slots of a candidate list,
in order — the list the site contraction consumes. -/
def d4CandPairs (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) :
    List (LayerColumn 2 × Fin 2) → List (Fin 2 × Fin 2)
  | [] => []
  | (P, s) :: rest => if h : τof P = .std
      then e ⟨⟨P, h⟩, s⟩ :: d4CandPairs τof e rest
      else d4CandPairs τof e rest

theorem d4CandPairs_eq_map (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2)
    (cands : List (LayerColumn 2 × Fin 2)) :
    d4CandPairs τof e cands = (d4CandSlots τof cands).map e := by
  induction cands with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨P, s⟩ := hd
    show (if h : τof P = .std
        then e ⟨⟨P, h⟩, s⟩ :: d4CandPairs τof e rest
        else d4CandPairs τof e rest)
      = (if h : τof P = .std
          then (⟨⟨P, h⟩, s⟩ :: d4CandSlots τof rest)
          else d4CandSlots τof rest).map e
    split_ifs with h
    · rw [List.map_cons, ih]
    · exact ih

/-- **(Candidate split)** The product of a site's candidate
factors is the accumulated sign character times the product
of the `std` entries over the site's end-pair list. -/
theorem d4_cand_split (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (a : DihedralGroup 4)
    (cands : List (LayerColumn 2 × Fin 2)) :
    (cands.map (d4CandFactor τof e a)).prod
      = d4Char (d4CandKlein τof cands) a
        * ((d4CandPairs τof e cands).map
            (fun p => nbRepMat a p.1 p.2)).prod := by
  induction cands with
  | nil =>
    show (1 : ℂ) = d4Char .triv a * 1
    rw [show d4Char .triv a = 1 from rfl, mul_one]
  | cons hd rest ih =>
    obtain ⟨P, s⟩ := hd
    rw [List.map_cons, List.prod_cons, ih]
    by_cases h : τof P = .std
    · have hfac : d4CandFactor τof e a (P, s)
          = nbRepMat a (e ⟨⟨P, h⟩, s⟩).1 (e ⟨⟨P, h⟩, s⟩).2 := by
        show (if h' : τof P = .std
            then nbRepMat a (e ⟨⟨P, h'⟩, s⟩).1 (e ⟨⟨P, h'⟩, s⟩).2
            else d4Char (τof P) a) = _
        rw [dif_pos h]
      have hklein : d4CandKlein τof ((P, s) :: rest)
          = d4CandKlein τof rest := by
        show (if τof P = .std then d4CandKlein τof rest else _) = _
        rw [if_pos h]
      have hpairs : d4CandPairs τof e ((P, s) :: rest)
          = e ⟨⟨P, h⟩, s⟩ :: d4CandPairs τof e rest := by
        show (if h' : τof P = .std
            then e ⟨⟨P, h'⟩, s⟩ :: d4CandPairs τof e rest
            else d4CandPairs τof e rest) = _
        rw [dif_pos h]
      rw [hfac, hklein, hpairs, List.map_cons, List.prod_cons]
      ring
    · have hfac : d4CandFactor τof e a (P, s)
          = d4Char (τof P) a := by
        show (if h' : τof P = .std then _ else d4Char (τof P) a) = _
        rw [dif_neg h]
      have hklein : d4CandKlein τof ((P, s) :: rest)
          = d4Klein (τof P) (d4CandKlein τof rest) := by
        show (if τof P = .std then _
          else d4Klein (τof P) (d4CandKlein τof rest)) = _
        rw [if_neg h]
      have hpairs : d4CandPairs τof e ((P, s) :: rest)
          = d4CandPairs τof e rest := by
        show (if h' : τof P = .std then _
          else d4CandPairs τof e rest) = _
        rw [dif_neg h]
      rw [hfac, hklein, hpairs, d4Char_klein (τof P)
        (d4CandKlein τof rest) (d4Type_sign_of_ne_std h)
        (d4CandKlein_sign τof rest) a]
      ring

theorem layerShift_two_eq_iff {ν : Fin 4} (hν : ν ≠ 0)
    (c c' : LayerSite 2) :
    layerShift ν hν c' = c ↔ c' = layerShift ν hν c := by
  constructor
  · intro h
    have hinv := layerShift_two_involutive ν hν c'
    rw [h] at hinv
    exact hinv.symm
  · intro h
    rw [h, layerShift_two_involutive]

/-- A nonzero element of `Fin 4` is `1`, `2` or `3`. -/
theorem fin_four_ne_zero {ν : Fin 4} (h : ν ≠ 0) :
    ν = 1 ∨ ν = 2 ∨ ν = 3 := by
  fin_cases ν <;> simp_all

/-- The columns based at `c` are exactly `(c, 1), (c, 2),
(c, 3)`. -/
theorem d4_filter_base (c : LayerSite 2) :
    Finset.univ.filter (fun P : LayerColumn 2 => P.1 = c)
      = {⟨c, ⟨1, by decide⟩⟩, ⟨c, ⟨2, by decide⟩⟩,
        ⟨c, ⟨3, by decide⟩⟩} := by
  ext ⟨c', ⟨ν, hν⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hc' : c' = c := h
    have hν3 : ν = 1 ∨ ν = 2 ∨ ν = 3 := fin_four_ne_zero hν
    subst hc'
    rcases hν3 with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with h | h | h
    · exact congrArg Prod.fst h
    · exact congrArg Prod.fst h
    · exact congrArg Prod.fst h

/-- The columns whose shift lands at `c` are exactly the
in-columns `(σ_ν c, ν)`, `ν ∈ {1, 2, 3}`. -/
theorem d4_filter_target (c : LayerSite 2) :
    Finset.univ.filter (fun P : LayerColumn 2 =>
        layerShift P.2.1 P.2.2 P.1 = c)
      = {⟨layerShift 1 (by decide) c, ⟨1, by decide⟩⟩,
        ⟨layerShift 2 (by decide) c, ⟨2, by decide⟩⟩,
        ⟨layerShift 3 (by decide) c, ⟨3, by decide⟩⟩} := by
  ext ⟨c', ⟨ν, hν⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hc' : c' = layerShift ν hν c :=
      (layerShift_two_eq_iff hν c c').mp h
    have hν3 : ν = 1 ∨ ν = 2 ∨ ν = 3 := fin_four_ne_zero hν
    subst hc'
    rcases hν3 with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with h | h | h
    · have h2 := congrArg
        (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1) h
      rwa [layerShift_two_involutive] at h2
    · have h2 := congrArg
        (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1) h
      rwa [layerShift_two_involutive] at h2
    · have h2 := congrArg
        (fun P : LayerColumn 2 => layerShift P.2.1 P.2.2 P.1) h
      rwa [layerShift_two_involutive] at h2

/-- **(Bracket)** The L7 regrouping bracket at a site — the
out-product at the base times the in-product at the target —
is the candidate factor product in list form. -/
theorem d4_bracket_eq (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (a : DihedralGroup 4)
    (c : LayerSite 2) :
    (∏ P ∈ Finset.univ.filter (fun P : LayerColumn 2 => P.1 = c),
        d4CandFactor τof e a (P, 0))
      * (∏ P ∈ Finset.univ.filter (fun P : LayerColumn 2 =>
          layerShift P.2.1 P.2.2 P.1 = c),
        d4CandFactor τof e a (P, 1))
      = ((d4CandList c).map (d4CandFactor τof e a)).prod := by
  have h12 : (⟨c, ⟨1, by decide⟩⟩ : LayerColumn 2)
      ≠ ⟨c, ⟨2, by decide⟩⟩ := by
    intro hh
    have h2 : (1 : Fin 4) = 2 :=
      congrArg (fun P : LayerColumn 2 => (P.2 : Fin 4)) hh
    exact absurd h2 (by decide)
  have h13 : (⟨c, ⟨1, by decide⟩⟩ : LayerColumn 2)
      ≠ ⟨c, ⟨3, by decide⟩⟩ := by
    intro hh
    have h2 : (1 : Fin 4) = 3 :=
      congrArg (fun P : LayerColumn 2 => (P.2 : Fin 4)) hh
    exact absurd h2 (by decide)
  have h23 : (⟨c, ⟨2, by decide⟩⟩ : LayerColumn 2)
      ≠ ⟨c, ⟨3, by decide⟩⟩ := by
    intro hh
    have h2 : (2 : Fin 4) = 3 :=
      congrArg (fun P : LayerColumn 2 => (P.2 : Fin 4)) hh
    exact absurd h2 (by decide)
  have g12 : (⟨layerShift 1 (by decide) c, ⟨1, by decide⟩⟩
        : LayerColumn 2)
      ≠ ⟨layerShift 2 (by decide) c, ⟨2, by decide⟩⟩ := by
    intro hh
    have h2 : (1 : Fin 4) = 2 :=
      congrArg (fun P : LayerColumn 2 => (P.2 : Fin 4)) hh
    exact absurd h2 (by decide)
  have g13 : (⟨layerShift 1 (by decide) c, ⟨1, by decide⟩⟩
        : LayerColumn 2)
      ≠ ⟨layerShift 3 (by decide) c, ⟨3, by decide⟩⟩ := by
    intro hh
    have h2 : (1 : Fin 4) = 3 :=
      congrArg (fun P : LayerColumn 2 => (P.2 : Fin 4)) hh
    exact absurd h2 (by decide)
  have g23 : (⟨layerShift 2 (by decide) c, ⟨2, by decide⟩⟩
        : LayerColumn 2)
      ≠ ⟨layerShift 3 (by decide) c, ⟨3, by decide⟩⟩ := by
    intro hh
    have h2 : (2 : Fin 4) = 3 :=
      congrArg (fun P : LayerColumn 2 => (P.2 : Fin 4)) hh
    exact absurd h2 (by decide)
  rw [d4_filter_base, d4_filter_target,
    Finset.prod_insert (by
      simp [Finset.mem_insert, Finset.mem_singleton, h12, h13]),
    Finset.prod_insert (by
      simp [Finset.mem_singleton, h23]),
    Finset.prod_singleton,
    Finset.prod_insert (by
      simp [Finset.mem_insert, Finset.mem_singleton, g12, g13]),
    Finset.prod_insert (by
      simp [Finset.mem_singleton, g23]),
    Finset.prod_singleton]
  show _ = ((d4CandList c).map (d4CandFactor τof e a)).prod
  simp only [d4CandList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  ring

/-- A sign character of a four-factor column word, split
into its `α`-part and its data part. -/
theorem d4Char_sign_colWord4 {τ : D4Type}
    (hτ : τ = .triv ∨ τ = .sgnA ∨ τ = .sgnB ∨ τ = .sgnC)
    (A B C D : DihedralGroup 4) :
    d4Char τ (A * B * C⁻¹ * D⁻¹)
      = (d4Char τ A * d4Char τ C) * (d4Char τ B * d4Char τ D) := by
  rw [d4Char_sign_mul τ hτ, d4Char_sign_mul τ hτ,
    d4Char_sign_mul τ hτ, d4Char_sign_inv τ hτ, d4Char_sign_inv τ hτ]
  ring

/-- **(Sign column split)** At a sign column, the character
of the column word is the product of the two candidate
`α`-factors and the two data characters. -/
theorem d4_sign_colWord_split (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (α : LayerSite 2 → DihedralGroup 4) (P : LayerColumn 2)
    (hP : τof P ≠ .std) :
    d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α)
      = (d4CandFactor τof e (α P.1) (P, 0)
          * d4CandFactor τof e
              (α (layerShift P.2.1 P.2.2 P.1)) (P, 1))
        * (d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2))
          * d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2))) := by
  have hsign := d4Type_sign_of_ne_std hP
  have hfac0 : d4CandFactor τof e (α P.1) (P, 0)
      = d4Char (τof P) (α P.1) := by
    show (if h' : τof P = .std then _ else d4Char (τof P) (α P.1))
      = _
    rw [dif_neg hP]
  have hfac1 : d4CandFactor τof e
        (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)
      = d4Char (τof P) (α (layerShift P.2.1 P.2.2 P.1)) := by
    show (if h' : τof P = .std then _
      else d4Char (τof P) (α (layerShift P.2.1 P.2.2 P.1))) = _
    rw [dif_neg hP]
  rw [hfac0, hfac1]
  show d4Char (τof P) (α P.1 * u' (layerLinkOf P.1 P.2.1 P.2.2)
      * (α (layerShift P.2.1 P.2.2 P.1))⁻¹
      * (u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹) = _
  rw [d4Char_sign_colWord4 hsign]

/-- The four-fold `Fin 2` sum of L5, repackaged as a sum
over the two end-pairs of a column. -/
theorem d4_sum_four_to_arrow
    (F : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ) :
    (∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ i₃ : Fin 2, ∑ i₄ : Fin 2,
        F i₁ i₂ i₃ i₄)
      = ∑ eP : Fin 2 → Fin 2 × Fin 2,
          F (eP 0).1 (eP 0).2 (eP 1).2 (eP 1).1 := by
  have h1 : (∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ i₃ : Fin 2,
        ∑ i₄ : Fin 2, F i₁ i₂ i₃ i₄)
      = ∑ eP : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
          F eP.1.1 eP.1.2 eP.2.2 eP.2.1 := by
    calc (∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ i₃ : Fin 2,
          ∑ i₄ : Fin 2, F i₁ i₂ i₃ i₄)
        = ∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ p : Fin 2 × Fin 2,
            F i₁ i₂ p.2 p.1 := by
          apply Finset.sum_congr rfl; intro i₁ _
          apply Finset.sum_congr rfl; intro i₂ _
          rw [Finset.sum_comm]
          exact (Fintype.sum_prod_type
            (fun p : Fin 2 × Fin 2 => F i₁ i₂ p.2 p.1)).symm
      _ = ∑ a : Fin 2 × Fin 2, ∑ p : Fin 2 × Fin 2,
            F a.1 a.2 p.2 p.1 :=
          (Fintype.sum_prod_type
            (fun a : Fin 2 × Fin 2 =>
              ∑ p : Fin 2 × Fin 2, F a.1 a.2 p.2 p.1)).symm
      _ = ∑ eP : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
            F eP.1.1 eP.1.2 eP.2.2 eP.2.1 :=
          (Fintype.sum_prod_type
            (fun eP : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
              F eP.1.1 eP.1.2 eP.2.2 eP.2.1)).symm
  rw [h1]
  exact (Fintype.sum_equiv (finTwoArrowEquiv (Fin 2 × Fin 2)) _ _
    (fun eP => rfl)).symm

/-- **(`std` column split)** At a `std` column, the character
of the column word is the sum over the column's end-pairs of
the `α`-entry product times the data-entry product (L5 with
the incoming `α`-entry transposed by L6/L6′). -/
theorem d4_std_colWord_expand (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (α : LayerSite 2 → DihedralGroup 4) (P : LayerColumn 2)
    (hP : τof P = .std) :
    d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α)
      = ∑ eP : Fin 2 → Fin 2 × Fin 2,
          (nbRepMat (α P.1) (eP 0).1 (eP 0).2
            * nbRepMat (α (layerShift P.2.1 P.2.2 P.1)) (eP 1).1
                (eP 1).2)
          * (nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) (eP 0).2
                (eP 1).2
            * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
                (eP 1).1 (eP 0).1) := by
  have hF : (∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ i₃ : Fin 2,
        ∑ i₄ : Fin 2,
        nbRepMat (α P.1) i₁ i₂
          * nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) i₂ i₃
          * nbRepMat ((α (layerShift P.2.1 P.2.2 P.1))⁻¹) i₃ i₄
          * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹) i₄ i₁)
      = ∑ i₁ : Fin 2, ∑ i₂ : Fin 2, ∑ i₃ : Fin 2, ∑ i₄ : Fin 2,
        nbRepMat (α P.1) i₁ i₂
          * nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) i₂ i₃
          * nbRepMat (α (layerShift P.2.1 P.2.2 P.1)) i₄ i₃
          * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹) i₄ i₁ := by
    apply Finset.sum_congr rfl; intro i₁ _
    apply Finset.sum_congr rfl; intro i₂ _
    apply Finset.sum_congr rfl; intro i₃ _
    apply Finset.sum_congr rfl; intro i₄ _
    rw [nbRepMat_inv_apply, nbRepMat_conj]
  rw [hP]
  show charFn nbRep (colWord u u' P.1 P.2.1 P.2.2 α) = _
  rw [charFn_nbRep_colWord_expand, hF,
    d4_sum_four_to_arrow (fun i₁ i₂ i₃ i₄ =>
      nbRepMat (α P.1) i₁ i₂
        * nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) i₂ i₃
        * nbRepMat (α (layerShift P.2.1 P.2.2 P.1)) i₄ i₃
        * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹) i₄ i₁)]
  apply Finset.sum_congr rfl; intro eP _
  ring

/-- The channel matrices have real entries. -/
theorem d4ChannelMat_star (b : Fin 4) (i j : Fin 2) :
    star (d4ChannelMat b i j) = d4ChannelMat b i j := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [d4ChannelMat]

/-- The channel contraction of a channel word along a slot
list, read through a slot-value function: the common form
of `d4SitePF` (row ends) and `d4SiteQF` (column ends). -/
def d4ChanProd (τof : LayerColumn 2 → D4Type) :
    List (Fin 4) → List (D4Slot τof) → (D4Slot τof → Fin 2) → ℂ
  | [], [], _ => 1
  | [], _ :: _, _ => 0
  | _ :: _, [], _ => 0
  | b :: bs, s :: s' :: rest, v =>
      d4ChannelMat b (v s) (v s') * d4ChanProd τof bs rest v
  | _ :: _, [_], _ => 0

/-- `d4SitePF`/`d4SiteQF` at an ends assignment are the
channel product read through the row/column ends. -/
theorem d4SitePF_chanProd (τof : LayerColumn 2 → D4Type) :
    ∀ (slots : List (D4Slot τof)),
      (∀ (bs : List (Fin 4)) (e : D4Slot τof → Fin 2 × Fin 2),
        d4SitePF bs (slots.map e)
          = d4ChanProd τof bs slots (fun s => (e s).1)
        ∧ d4SiteQF bs (slots.map e)
          = d4ChanProd τof bs slots (fun s => (e s).2))
      ∧ ∀ (s : D4Slot τof) (bs : List (Fin 4))
          (e : D4Slot τof → Fin 2 × Fin 2),
          d4SitePF bs ((s :: slots).map e)
            = d4ChanProd τof bs (s :: slots) (fun s => (e s).1)
          ∧ d4SiteQF bs ((s :: slots).map e)
            = d4ChanProd τof bs (s :: slots) (fun s => (e s).2) := by
  intro slots
  induction slots with
  | nil =>
    constructor
    · intro bs e
      cases bs with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs' => exact ⟨rfl, rfl⟩
    · intro s bs e
      cases bs with
      | nil => exact ⟨rfl, rfl⟩
      | cons b bs' => exact ⟨rfl, rfl⟩
  | cons s rest ih =>
    refine ⟨ih.2 s, fun s' bs e => ?_⟩
    cases bs with
    | nil => exact ⟨rfl, rfl⟩
    | cons b bs' =>
      constructor
      · show d4ChannelMat b (e s').1 (e s).1
            * d4SitePF bs' (rest.map e)
          = d4ChannelMat b (e s').1 (e s).1
            * d4ChanProd τof bs' rest (fun s => (e s).1)
        rw [(ih.1 bs' e).1]
      · show d4ChannelMat b (e s').2 (e s).2
            * d4SiteQF bs' (rest.map e)
          = d4ChannelMat b (e s').2 (e s).2
            * d4ChanProd τof bs' rest (fun s => (e s).2)
        rw [(ih.1 bs' e).2]

/-- The channel product is real. -/
theorem d4ChanProd_star (τof : LayerColumn 2 → D4Type) :
    ∀ (slots : List (D4Slot τof)),
      (∀ (bs : List (Fin 4)) (v : D4Slot τof → Fin 2),
        star (d4ChanProd τof bs slots v) = d4ChanProd τof bs slots v)
      ∧ ∀ (s : D4Slot τof) (bs : List (Fin 4))
          (v : D4Slot τof → Fin 2),
          star (d4ChanProd τof bs (s :: slots) v)
            = d4ChanProd τof bs (s :: slots) v := by
  intro slots
  induction slots with
  | nil =>
    constructor
    · intro bs v
      cases bs with
      | nil => simp [d4ChanProd]
      | cons b bs' => simp [d4ChanProd]
    · intro s bs v
      cases bs with
      | nil => simp [d4ChanProd]
      | cons b bs' => simp [d4ChanProd]
  | cons s rest ih =>
    refine ⟨ih.2 s, fun s' bs v => ?_⟩
    cases bs with
    | nil => simp [d4ChanProd]
    | cons b bs' =>
      show star (d4ChannelMat b (v s') (v s)
          * d4ChanProd τof bs' rest v)
        = d4ChannelMat b (v s') (v s) * d4ChanProd τof bs' rest v
      rw [star_mul, d4ChannelMat_star, (ih.1 bs' v), mul_comm]

/-- The data factor of a column at an ends assignment:
for a `std` column, the `u'`-entry at the column ends times
the `(u)⁻¹`-entry at the row ends; for a sign column, the
two data characters. -/
noncomputable def d4Data (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (e : D4Slot τof → Fin 2 × Fin 2) (P : LayerColumn 2) : ℂ :=
  if h : τof P = .std then
    nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) (e ⟨⟨P, h⟩, 0⟩).2
        (e ⟨⟨P, h⟩, 1⟩).2
      * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
          (e ⟨⟨P, h⟩, 1⟩).1 (e ⟨⟨P, h⟩, 0⟩).1
  else d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2))
    * d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2))

/-- The row-end data factor of a column. -/
noncomputable def d4DataR (τof : LayerColumn 2 → D4Type)
    (u : LayerLink 2 → DihedralGroup 4) (r : D4Slot τof → Fin 2)
    (P : LayerColumn 2) : ℂ :=
  if h : τof P = .std then
    nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹) (r ⟨⟨P, h⟩, 1⟩)
      (r ⟨⟨P, h⟩, 0⟩)
  else d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2))

/-- The column-end data factor of a column. -/
noncomputable def d4DataC (τof : LayerColumn 2 → D4Type)
    (u' : LayerLink 2 → DihedralGroup 4) (c : D4Slot τof → Fin 2)
    (P : LayerColumn 2) : ℂ :=
  if h : τof P = .std then
    nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) (c ⟨⟨P, h⟩, 0⟩)
      (c ⟨⟨P, h⟩, 1⟩)
  else d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2))

/-- The data factor splits into its row-end and column-end
parts. -/
theorem d4Data_split (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (e : D4Slot τof → Fin 2 × Fin 2) (r c : D4Slot τof → Fin 2)
    (h1 : ∀ s, (e s).1 = r s) (h2 : ∀ s, (e s).2 = c s)
    (P : LayerColumn 2) :
    d4Data τof u u' e P = d4DataR τof u r P * d4DataC τof u' c P := by
  by_cases h : τof P = .std
  · show (if h' : τof P = .std then
        nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2))
            (e ⟨⟨P, h'⟩, 0⟩).2 (e ⟨⟨P, h'⟩, 1⟩).2
          * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
              (e ⟨⟨P, h'⟩, 1⟩).1 (e ⟨⟨P, h'⟩, 0⟩).1
        else _) = _
    rw [dif_pos h]
    show _ = (if h' : τof P = .std then
        nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
          (r ⟨⟨P, h'⟩, 1⟩) (r ⟨⟨P, h'⟩, 0⟩) else _)
      * (if h' : τof P = .std then
        nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2)) (c ⟨⟨P, h'⟩, 0⟩)
          (c ⟨⟨P, h'⟩, 1⟩) else _)
    rw [dif_pos h, dif_pos h, h1 ⟨⟨P, h⟩, 1⟩, h1 ⟨⟨P, h⟩, 0⟩,
      h2 ⟨⟨P, h⟩, 0⟩, h2 ⟨⟨P, h⟩, 1⟩]
    ring
  · show (if h' : τof P = .std then _
        else d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2))
          * d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2))) = _
    rw [dif_neg h]
    show _ = (if h' : τof P = .std then _
        else d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2)))
      * (if h' : τof P = .std then _
        else d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2)))
    rw [dif_neg h, dif_neg h, mul_comm]

/-- The row-end feature: the sum over row ends of the
row-data product times the site channel products. -/
noncomputable def d4Phi (τof : LayerColumn 2 → D4Type)
    (κ : LayerSite 2 → List (Fin 4))
    (u : LayerLink 2 → DihedralGroup 4) : ℂ :=
  ∑ r : D4Slot τof → Fin 2,
    (∏ P : LayerColumn 2, d4DataR τof u r P)
      * ∏ c : LayerSite 2,
        d4ChanProd τof (κ c) (d4CandSlots τof (d4CandList c)) r

/-- The column-end feature; it equals the row-end feature
at the same configuration (the transpose identity L6/L6′),
which is the Gram symmetry of the separation. -/
noncomputable def d4Psi (τof : LayerColumn 2 → D4Type)
    (κ : LayerSite 2 → List (Fin 4))
    (u' : LayerLink 2 → DihedralGroup 4) : ℂ :=
  ∑ c : D4Slot τof → Fin 2,
    (∏ P : LayerColumn 2, d4DataC τof u' c P)
      * ∏ s : LayerSite 2,
        d4ChanProd τof (κ s) (d4CandSlots τof (d4CandList s)) c

theorem d4DataR_star (τof : LayerColumn 2 → D4Type)
    (u : LayerLink 2 → DihedralGroup 4) (r : D4Slot τof → Fin 2)
    (P : LayerColumn 2) :
    star (d4DataR τof u r P) = d4DataR τof u r P := by
  by_cases h : τof P = .std
  · show star (if h' : τof P = .std then
        nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
          (r ⟨⟨P, h'⟩, 1⟩) (r ⟨⟨P, h'⟩, 0⟩) else _)
      = (if h' : τof P = .std then
        nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
          (r ⟨⟨P, h'⟩, 1⟩) (r ⟨⟨P, h'⟩, 0⟩) else _)
    rw [dif_pos h]
    exact nbRepMat_conj _ _ _
  · show star (if h' : τof P = .std then _
        else d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2)))
      = (if h' : τof P = .std then _
        else d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2)))
    rw [dif_neg h]
    exact d4Char_sign_star _ (d4Type_sign_of_ne_std h) _

theorem d4Phi_star (τof : LayerColumn 2 → D4Type)
    (κ : LayerSite 2 → List (Fin 4))
    (u : LayerLink 2 → DihedralGroup 4) :
    star (d4Phi τof κ u) = d4Phi τof κ u := by
  show star (∑ r : D4Slot τof → Fin 2,
      (∏ P : LayerColumn 2, d4DataR τof u r P)
        * ∏ c : LayerSite 2,
          d4ChanProd τof (κ c) (d4CandSlots τof (d4CandList c)) r) = _
  rw [star_sum]
  apply Finset.sum_congr rfl; intro r _
  have hP : ∏ P : LayerColumn 2, star (d4DataR τof u r P)
      = ∏ P : LayerColumn 2, d4DataR τof u r P :=
    Finset.prod_congr rfl fun P _ => d4DataR_star τof u r P
  have hC : ∏ c : LayerSite 2,
        star (d4ChanProd τof (κ c) (d4CandSlots τof (d4CandList c)) r)
      = ∏ c : LayerSite 2,
        d4ChanProd τof (κ c) (d4CandSlots τof (d4CandList c)) r :=
    Finset.prod_congr rfl fun c _ => (d4ChanProd_star τof _).1 _ _
  rw [star_mul, star_prod, star_prod, hP, hC, mul_comm]

theorem d4Psi_eq_phi (τof : LayerColumn 2 → D4Type)
    (κ : LayerSite 2 → List (Fin 4))
    (u : LayerLink 2 → DihedralGroup 4) :
    d4Psi τof κ u = d4Phi τof κ u := by
  apply Finset.sum_congr rfl; intro v _
  congr 1
  apply Finset.prod_congr rfl; intro P _
  by_cases h : τof P = .std
  · show (if h' : τof P = .std then
        nbRepMat (u (layerLinkOf P.1 P.2.1 P.2.2)) (v ⟨⟨P, h'⟩, 0⟩)
          (v ⟨⟨P, h'⟩, 1⟩) else _)
      = (if h' : τof P = .std then
        nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
          (v ⟨⟨P, h'⟩, 1⟩) (v ⟨⟨P, h'⟩, 0⟩) else _)
    rw [dif_pos h, dif_pos h, nbRepMat_inv_apply, nbRepMat_conj]
  · show (if h' : τof P = .std then _
        else d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2)))
      = (if h' : τof P = .std then _
        else d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2)))
    rw [dif_neg h, dif_neg h]

/-- The number of pairwise contraction nodes at a site:
half the number of `std` slots there. -/
def d4PairCount (τof : LayerColumn 2 → D4Type) (c : LayerSite 2) :
    ℕ :=
  (d4CandSlots τof (d4CandList c)).length / 2

theorem d4CandPairs_length (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (c : LayerSite 2) :
    (d4CandPairs τof e (d4CandList c)).length
      = (d4CandSlots τof (d4CandList c)).length := by
  rw [d4CandPairs_eq_map, List.length_map]

/-- The site separation, with the channel index transported
to the `std`-slot count (independent of the ends). -/
theorem d4_site_sep (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (c : LayerSite 2) :
    d4SiteContract (d4CandKlein τof (d4CandList c))
        (d4CandPairs τof e (d4CandList c))
      = ∑ bs : Fin (d4PairCount τof c) → Fin 4,
          d4SiteCoeff (d4CandKlein τof (d4CandList c))
              (List.ofFn bs)
            * d4SitePF (List.ofFn bs)
                (d4CandPairs τof e (d4CandList c))
            * d4SiteQF (List.ofFn bs)
                (d4CandPairs τof e (d4CandList c)) := by
  have h := d4_siteContract_sep (d4CandKlein τof (d4CandList c))
    (d4CandPairs τof e (d4CandList c))
  rw [d4CandPairs_length] at h
  exact h

/-- The site sum: the candidate-factor sum at a site is the
separated channel sum. -/
theorem d4_site_sum (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (c : LayerSite 2) :
    (∑ a : DihedralGroup 4,
        ((d4CandList c).map (d4CandFactor τof e a)).prod)
      = ∑ bs : Fin (d4PairCount τof c) → Fin 4,
          d4SiteCoeff (d4CandKlein τof (d4CandList c))
              (List.ofFn bs)
            * d4SitePF (List.ofFn bs)
                (d4CandPairs τof e (d4CandList c))
            * d4SiteQF (List.ofFn bs)
                (d4CandPairs τof e (d4CandList c)) := by
  rw [← d4_site_sep]
  calc (∑ a : DihedralGroup 4,
        ((d4CandList c).map (d4CandFactor τof e a)).prod)
      = ∑ a : DihedralGroup 4,
          d4Char (d4CandKlein τof (d4CandList c)) a
            * ((d4CandPairs τof e (d4CandList c)).map
                (fun p => nbRepMat a p.1 p.2)).prod := by
        apply Finset.sum_congr rfl; intro a _
        exact d4_cand_split τof e a (d4CandList c)
    _ = d4SiteContract (d4CandKlein τof (d4CandList c))
          (d4CandPairs τof e (d4CandList c)) :=
        d4_site_sum_contract _ (d4CandKlein_sign τof (d4CandList c)) _

theorem d4CandFactor_std (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (a : DihedralGroup 4)
    {P : LayerColumn 2} (h : τof P = .std) (s : Fin 2) :
    d4CandFactor τof e a (P, s)
      = nbRepMat a (e ⟨⟨P, h⟩, s⟩).1 (e ⟨⟨P, h⟩, s⟩).2 := by
  show (if h' : τof P = .std then
      nbRepMat a (e ⟨⟨P, h'⟩, s⟩).1 (e ⟨⟨P, h'⟩, s⟩).2 else _) = _
  rw [dif_pos h]

theorem d4CandFactor_sign (τof : LayerColumn 2 → D4Type)
    (e : D4Slot τof → Fin 2 × Fin 2) (a : DihedralGroup 4)
    {P : LayerColumn 2} (h : τof P ≠ .std) (s : Fin 2) :
    d4CandFactor τof e a (P, s) = d4Char (τof P) a := by
  show (if h' : τof P = .std then _ else d4Char (τof P) a) = _
  rw [dif_neg h]

theorem d4Data_std (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (e : D4Slot τof → Fin 2 × Fin 2) {P : LayerColumn 2}
    (h : τof P = .std) :
    d4Data τof u u' e P
      = nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2))
          (e ⟨⟨P, h⟩, 0⟩).2 (e ⟨⟨P, h⟩, 1⟩).2
        * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
            (e ⟨⟨P, h⟩, 1⟩).1 (e ⟨⟨P, h⟩, 0⟩).1 := by
  show (if h' : τof P = .std then
      nbRepMat (u' (layerLinkOf P.1 P.2.1 P.2.2))
          (e ⟨⟨P, h'⟩, 0⟩).2 (e ⟨⟨P, h'⟩, 1⟩).2
        * nbRepMat ((u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹)
            (e ⟨⟨P, h'⟩, 1⟩).1 (e ⟨⟨P, h'⟩, 0⟩).1
      else _) = _
  rw [dif_pos h]

theorem d4Data_sign (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (e : D4Slot τof → Fin 2 × Fin 2) {P : LayerColumn 2}
    (h : τof P ≠ .std) :
    d4Data τof u u' e P
      = d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2))
        * d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2)) := by
  show (if h' : τof P = .std then _
      else d4Char (τof P) (u' (layerLinkOf P.1 P.2.1 P.2.2))
        * d4Char (τof P) (u (layerLinkOf P.1 P.2.1 P.2.2))) = _
  rw [dif_neg h]

/-- Slot ends, curried and uncurried. -/
def d4SlotEndsEquiv (τof : LayerColumn 2 → D4Type) :
    (∀ P : D4StdCol τof, Fin 2 → Fin 2 × Fin 2)
      ≃ (D4Slot τof → Fin 2 × Fin 2) where
  toFun E s := E s.1 s.2
  invFun e P s := e ⟨P, s⟩
  left_inv E := by funext P s; rfl
  right_inv e := by funext ⟨P, s⟩; rfl

/-- Ends, split into row ends and column ends. -/
def d4EndsSplitEquiv (τof : LayerColumn 2 → D4Type) :
    (D4Slot τof → Fin 2 × Fin 2)
      ≃ (D4Slot τof → Fin 2) × (D4Slot τof → Fin 2) where
  toFun e := (fun s => (e s).1, fun s => (e s).2)
  invFun p s := (p.1 s, p.2 s)
  left_inv e := by funext s; rfl
  right_inv p := by cases p with | mk r c => rfl

/-- The total channel weight of a global channel assignment:
the product over sites of the site coefficient's real
form. -/
noncomputable def d4Weight (τof : LayerColumn 2 → D4Type)
    (κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4) : ℝ :=
  ∏ c : LayerSite 2,
    (1 / 2 : ℝ) ^ (d4PairCount τof c)
      * (if (List.ofFn (κ c)).foldl
            (fun acc b => d4Klein acc (d4TauChan b))
            (d4CandKlein τof (d4CandList c)) = .triv
          then 8 else 0)

theorem d4Weight_nonneg (τof : LayerColumn 2 → D4Type)
    (κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4) :
    0 ≤ d4Weight τof κ := by
  apply Finset.prod_nonneg
  intro c _
  apply mul_nonneg (pow_nonneg (by norm_num) _)
  split_ifs <;> norm_num

/-- The product of the site coefficients is the cast of the
total weight. -/
theorem d4_coeff_prod_eq (τof : LayerColumn 2 → D4Type)
    (κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4) :
    (∏ c : LayerSite 2, d4SiteCoeff (d4CandKlein τof (d4CandList c))
        (List.ofFn (κ c)))
      = ((d4Weight τof κ : ℝ) : ℂ) := by
  show _ = ((∏ c : LayerSite 2,
      (1 / 2 : ℝ) ^ (d4PairCount τof c)
        * (if (List.ofFn (κ c)).foldl
              (fun acc b => d4Klein acc (d4TauChan b))
              (d4CandKlein τof (d4CandList c)) = .triv
            then 8 else 0) : ℝ) : ℂ)
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl; intro c _
  show (((1 / 2 : ℝ) ^ (List.ofFn (κ c)).length
      * (if (List.ofFn (κ c)).foldl
            (fun acc b => d4Klein acc (d4TauChan b))
            (d4CandKlein τof (d4CandList c)) = .triv
          then 8 else 0) : ℝ) : ℂ) = _
  rw [List.length_ofFn]

/-- The Gram feature of a global channel assignment. -/
noncomputable def d4Feat (τof : LayerColumn 2 → D4Type)
    (κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4)
    (u : LayerLink 2 → DihedralGroup 4) : ℂ :=
  ((Real.sqrt (d4Weight τof κ) : ℂ))
    * d4Phi τof (fun c => List.ofFn (κ c)) u

example (w : ℝ) : star ((Real.sqrt w : ℂ)) = (Real.sqrt w : ℂ) := by
  simp

/-- The raw entry form of a `std` column's split summand is
the candidate-factor product times the data factor. -/
theorem d4_std_factor_eq (τof : LayerColumn 2 → D4Type)
    (ê : D4Slot τof → Fin 2 × Fin 2)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (α : LayerSite 2 → DihedralGroup 4) (P : D4StdCol τof) :
    (nbRepMat (α P.1.1) (ê ⟨P, 0⟩).1 (ê ⟨P, 0⟩).2
      * nbRepMat (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (ê ⟨P, 1⟩).1
          (ê ⟨P, 1⟩).2)
    * (nbRepMat (u' (layerLinkOf P.1.1 P.1.2.1 P.1.2.2)) (ê ⟨P, 0⟩).2
          (ê ⟨P, 1⟩).2
      * nbRepMat ((u (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))⁻¹)
          (ê ⟨P, 1⟩).1 (ê ⟨P, 0⟩).1)
    = (d4CandFactor τof ê (α P.1.1) (P.1, 0)
        * d4CandFactor τof ê
            (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
      * d4Data τof u u' ê P.1 := by
  rw [d4CandFactor_std τof ê _ P.2 0, d4CandFactor_std τof ê _ P.2 1,
    d4Data_std τof u u' ê P.2]

/-- `d4_std_factor_eq` at the curried ends assignment, in
the `(E P)` form the product-of-sums expansion produces. -/
theorem d4_std_factor_eq' (τof : LayerColumn 2 → D4Type)
    (E : ∀ P : D4StdCol τof, Fin 2 → Fin 2 × Fin 2)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (α : LayerSite 2 → DihedralGroup 4) (P : D4StdCol τof) :
    (nbRepMat (α P.1.1) ((E P) 0).1 ((E P) 0).2
      * nbRepMat (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) ((E P) 1).1
          ((E P) 1).2)
    * (nbRepMat (u' (layerLinkOf P.1.1 P.1.2.1 P.1.2.2)) ((E P) 0).2
          ((E P) 1).2
      * nbRepMat ((u (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))⁻¹)
          ((E P) 1).1 ((E P) 0).1)
    = (d4CandFactor τof (d4SlotEndsEquiv τof E) (α P.1.1) (P.1, 0)
        * d4CandFactor τof (d4SlotEndsEquiv τof E)
            (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
      * d4Data τof u u' (d4SlotEndsEquiv τof E) P.1 :=
  d4_std_factor_eq τof (d4SlotEndsEquiv τof E) u u' α P

/-- The `std`-column product over a pattern expands into
the sum over global ends assignments of the candidate/data
factor products. -/
theorem d4_std_prod_expand (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (α : LayerSite 2 → DihedralGroup 4) :
    (∏ P ∈ Finset.univ.filter (fun P : LayerColumn 2 => τof P = .std),
        d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
      = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          ∏ P : D4StdCol τof,
            ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
              * d4CandFactor τof ê
                  (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
            * d4Data τof u u' ê P.1) := by
  rw [Finset.prod_subtype (Finset.univ.filter
      (fun P : LayerColumn 2 => τof P = .std))
    (fun x => Finset.mem_filter.trans
      (and_iff_right (Finset.mem_univ x)))]
  calc (∏ P : D4StdCol τof,
        d4Char (τof P.1) (colWord u u' P.1.1 P.1.2.1 P.1.2.2 α))
      = ∏ P : D4StdCol τof, ∑ eP : Fin 2 → Fin 2 × Fin 2,
          (nbRepMat (α P.1.1) (eP 0).1 (eP 0).2
            * nbRepMat (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (eP 1).1
                (eP 1).2)
          * (nbRepMat (u' (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))
                (eP 0).2 (eP 1).2
            * nbRepMat ((u (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))⁻¹)
                (eP 1).1 (eP 0).1) := by
        apply Finset.prod_congr rfl; intro P _
        exact d4_std_colWord_expand τof u u' α P.1 P.2
    _ = ∑ E : ∀ P : D4StdCol τof, Fin 2 → Fin 2 × Fin 2,
          ∏ P : D4StdCol τof,
            (nbRepMat (α P.1.1) ((E P) 0).1 ((E P) 0).2
              * nbRepMat (α (layerShift P.1.2.1 P.1.2.2 P.1.1))
                  ((E P) 1).1 ((E P) 1).2)
            * (nbRepMat (u' (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))
                  ((E P) 0).2 ((E P) 1).2
              * nbRepMat ((u (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))⁻¹)
                  ((E P) 1).1 ((E P) 0).1) :=
        Fintype.prod_sum
          (fun (P : D4StdCol τof) (eP : Fin 2 → Fin 2 × Fin 2) =>
            (nbRepMat (α P.1.1) (eP 0).1 (eP 0).2
              * nbRepMat (α (layerShift P.1.2.1 P.1.2.2 P.1.1))
                  (eP 1).1 (eP 1).2)
            * (nbRepMat (u' (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))
                  (eP 0).2 (eP 1).2
              * nbRepMat ((u (layerLinkOf P.1.1 P.1.2.1 P.1.2.2))⁻¹)
                  (eP 1).1 (eP 0).1))
    _ = ∑ E : ∀ P : D4StdCol τof, Fin 2 → Fin 2 × Fin 2,
          ∏ P : D4StdCol τof,
            ((d4CandFactor τof (d4SlotEndsEquiv τof E) (α P.1.1)
                (P.1, 0)
              * d4CandFactor τof (d4SlotEndsEquiv τof E)
                  (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
            * d4Data τof u u' (d4SlotEndsEquiv τof E) P.1) := by
        apply Finset.sum_congr rfl; intro E _
        apply Finset.prod_congr rfl; intro P _
        exact d4_std_factor_eq' τof E u u' α P
    _ = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          ∏ P : D4StdCol τof,
            ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
              * d4CandFactor τof ê
                  (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
            * d4Data τof u u' ê P.1) :=
        Equiv.sum_comp (d4SlotEndsEquiv τof)
          (fun ê : D4Slot τof → Fin 2 × Fin 2 =>
            ∏ P : D4StdCol τof,
              ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
              * d4Data τof u u' ê P.1))

/-- The sign-column product over a pattern splits into its
candidate-factor product and its data product. -/
theorem d4_sign_prod_split (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4)
    (α : LayerSite 2 → DihedralGroup 4)
    (ê : D4Slot τof → Fin 2 × Fin 2) :
    (∏ P ∈ Finset.univ.filter
        (fun P : LayerColumn 2 => ¬ τof P = .std),
        d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
      = (∏ P ∈ Finset.univ.filter
            (fun P : LayerColumn 2 => ¬ τof P = .std),
            d4CandFactor τof ê (α P.1) (P, 0)
              * d4CandFactor τof ê
                  (α (layerShift P.2.1 P.2.2 P.1)) (P, 1))
        * (∏ P ∈ Finset.univ.filter
            (fun P : LayerColumn 2 => ¬ τof P = .std),
            d4Data τof u u' ê P) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro P hP
  have hP' : τof P ≠ .std := (Finset.mem_filter.mp hP).2
  rw [d4_sign_colWord_split τof ê u u' α P hP',
    d4Data_sign τof u u' ê hP']

/-- The ends sum of the data/PF/QF product is the product
of the row-end feature and the column-end feature. -/
theorem d4_ends_factor (τof : LayerColumn 2 → D4Type)
    (κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4)
    (u u' : LayerLink 2 → DihedralGroup 4) :
    (∑ ê : D4Slot τof → Fin 2 × Fin 2,
        (∏ P : LayerColumn 2, d4Data τof u u' ê P)
          * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
              (d4CandPairs τof ê (d4CandList c)))
          * (∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
              (d4CandPairs τof ê (d4CandList c))))
      = d4Phi τof (fun c => List.ofFn (κ c)) u
          * d4Psi τof (fun c => List.ofFn (κ c)) u' := by
  calc (∑ ê : D4Slot τof → Fin 2 × Fin 2,
        (∏ P : LayerColumn 2, d4Data τof u u' ê P)
          * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
              (d4CandPairs τof ê (d4CandList c)))
          * (∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
              (d4CandPairs τof ê (d4CandList c))))
      = ∑ p : (D4Slot τof → Fin 2) × (D4Slot τof → Fin 2),
          (∏ P : LayerColumn 2,
              d4Data τof u u' ((d4EndsSplitEquiv τof).invFun p) P)
            * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                (d4CandPairs τof ((d4EndsSplitEquiv τof).invFun p)
                  (d4CandList c)))
            * (∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                (d4CandPairs τof ((d4EndsSplitEquiv τof).invFun p)
                  (d4CandList c))) :=
        (Fintype.sum_equiv (d4EndsSplitEquiv τof).symm
          (fun p : (D4Slot τof → Fin 2) × (D4Slot τof → Fin 2) =>
            (∏ P : LayerColumn 2,
                d4Data τof u u' ((d4EndsSplitEquiv τof).invFun p) P)
              * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                  (d4CandPairs τof ((d4EndsSplitEquiv τof).invFun p)
                    (d4CandList c)))
              * (∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                  (d4CandPairs τof ((d4EndsSplitEquiv τof).invFun p)
                    (d4CandList c))))
          (fun ê : D4Slot τof → Fin 2 × Fin 2 =>
            (∏ P : LayerColumn 2, d4Data τof u u' ê P)
              * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                  (d4CandPairs τof ê (d4CandList c)))
              * (∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                  (d4CandPairs τof ê (d4CandList c))))
          (fun p => rfl)).symm
    _ = ∑ p : (D4Slot τof → Fin 2) × (D4Slot τof → Fin 2),
          ((∏ P : LayerColumn 2, d4DataR τof u p.1 P)
            * ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                (d4CandSlots τof (d4CandList c)) p.1)
          * ((∏ P : LayerColumn 2, d4DataC τof u' p.2 P)
            * ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                (d4CandSlots τof (d4CandList c)) p.2) := by
        apply Finset.sum_congr rfl; intro p _
        have hdata : (∏ P : LayerColumn 2,
              d4Data τof u u' ((d4EndsSplitEquiv τof).invFun p) P)
            = (∏ P : LayerColumn 2, d4DataR τof u p.1 P)
              * ∏ P : LayerColumn 2, d4DataC τof u' p.2 P := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl; intro P _
          exact d4Data_split τof u u' _ p.1 p.2 (fun s => rfl)
            (fun s => rfl) P
        have hPF : (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
              (d4CandPairs τof ((d4EndsSplitEquiv τof).invFun p)
                (d4CandList c)))
            = ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                (d4CandSlots τof (d4CandList c)) p.1 := by
          apply Finset.prod_congr rfl; intro c _
          rw [d4CandPairs_eq_map]
          exact ((d4SitePF_chanProd τof
            (d4CandSlots τof (d4CandList c))).1 (List.ofFn (κ c))
            ((d4EndsSplitEquiv τof).invFun p)).1
        have hQF : (∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
              (d4CandPairs τof ((d4EndsSplitEquiv τof).invFun p)
                (d4CandList c)))
            = ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                (d4CandSlots τof (d4CandList c)) p.2 := by
          apply Finset.prod_congr rfl; intro c _
          rw [d4CandPairs_eq_map]
          exact ((d4SitePF_chanProd τof
            (d4CandSlots τof (d4CandList c))).1 (List.ofFn (κ c))
            ((d4EndsSplitEquiv τof).invFun p)).2
        rw [hdata, hPF, hQF]; ring
    _ = (∑ r : D4Slot τof → Fin 2,
          (∏ P : LayerColumn 2, d4DataR τof u r P)
            * ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                (d4CandSlots τof (d4CandList c)) r)
        * (∑ c : D4Slot τof → Fin 2,
          (∏ P : LayerColumn 2, d4DataC τof u' c P)
            * ∏ s : LayerSite 2, d4ChanProd τof (List.ofFn (κ s))
                (d4CandSlots τof (d4CandList s)) c) :=
        (Fintype.sum_prod_type
          (fun p : (D4Slot τof → Fin 2) × (D4Slot τof → Fin 2) =>
            ((∏ P : LayerColumn 2, d4DataR τof u p.1 P)
              * ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                  (d4CandSlots τof (d4CandList c)) p.1)
            * ((∏ P : LayerColumn 2, d4DataC τof u' p.2 P)
              * ∏ s : LayerSite 2, d4ChanProd τof (List.ofFn (κ s))
                  (d4CandSlots τof (d4CandList s)) p.2))).trans
          (Finset.sum_mul_sum Finset.univ Finset.univ
            (fun r : D4Slot τof → Fin 2 =>
              (∏ P : LayerColumn 2, d4DataR τof u r P)
                * ∏ c : LayerSite 2, d4ChanProd τof (List.ofFn (κ c))
                    (d4CandSlots τof (d4CandList c)) r)
            (fun c : D4Slot τof → Fin 2 =>
              (∏ P : LayerColumn 2, d4DataC τof u' c P)
                * ∏ s : LayerSite 2, d4ChanProd τof (List.ofFn (κ s))
                    (d4CandSlots τof (d4CandList s)) c)).symm
    _ = d4Phi τof (fun c => List.ofFn (κ c)) u
          * d4Psi τof (fun c => List.ofFn (κ c)) u' := rfl

/-- **(Assembly)** The stratum sum of a type assignment is
the Gram sum of the features `d4Feat`: the column splits,
the site regrouping (L7), the site factorization (L8), the
site separations, the ends factorization, and the weight
extraction, composed. -/
theorem d4_stratum_gram (τof : LayerColumn 2 → D4Type)
    (u u' : LayerLink 2 → DihedralGroup 4) :
    (∑ α : LayerSite 2 → DihedralGroup 4,
        ∏ P : LayerColumn 2,
          d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
      = ∑ κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4,
          d4Feat τof κ u * star (d4Feat τof κ u') := by
  calc (∑ α : LayerSite 2 → DihedralGroup 4,
        ∏ P : LayerColumn 2,
          d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
      = ∑ α : LayerSite 2 → DihedralGroup 4,
          (∏ P ∈ Finset.univ.filter
              (fun P : LayerColumn 2 => τof P = .std),
            d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
          * ∏ P ∈ Finset.univ.filter
              (fun P : LayerColumn 2 => ¬ τof P = .std),
              d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α) := by
        apply Finset.sum_congr rfl; intro α _
        exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    _ = ∑ α : LayerSite 2 → DihedralGroup 4,
          (∑ ê : D4Slot τof → Fin 2 × Fin 2,
            ∏ P : D4StdCol τof,
              ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
              * d4Data τof u u' ê P.1))
          * ∏ P ∈ Finset.univ.filter
              (fun P : LayerColumn 2 => ¬ τof P = .std),
              d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α) := by
        apply Finset.sum_congr rfl; intro α _
        rw [d4_std_prod_expand τof u u' α]
    _ = ∑ α : LayerSite 2 → DihedralGroup 4,
          ∑ ê : D4Slot τof → Fin 2 × Fin 2,
            (∏ P : D4StdCol τof,
              ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
              * d4Data τof u u' ê P.1))
            * ∏ P ∈ Finset.univ.filter
                (fun P : LayerColumn 2 => ¬ τof P = .std),
                d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α) := by
        apply Finset.sum_congr rfl; intro α _
        rw [Finset.sum_mul]
    _ = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          ∑ α : LayerSite 2 → DihedralGroup 4,
            (∏ P : D4StdCol τof,
              ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
              * d4Data τof u u' ê P.1))
            * ∏ P ∈ Finset.univ.filter
                (fun P : LayerColumn 2 => ¬ τof P = .std),
                d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α) :=
        Finset.sum_comm
    _ = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          (∏ P : LayerColumn 2, d4Data τof u u' ê P)
          * ∑ α : LayerSite 2 → DihedralGroup 4,
              ∏ P : LayerColumn 2,
                (d4CandFactor τof ê (α P.1) (P, 0)
                  * d4CandFactor τof ê
                      (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)) := by
        apply Finset.sum_congr rfl; intro ê _
        have hf : ∀ α : LayerSite 2 → DihedralGroup 4,
            (∏ P : LayerColumn 2,
              (d4CandFactor τof ê (α P.1) (P, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)))
            = (∏ P : D4StdCol τof,
                (d4CandFactor τof ê (α P.1.1) (P.1, 0)
                  * d4CandFactor τof ê
                      (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1)))
              * ∏ P ∈ Finset.univ.filter
                  (fun P : LayerColumn 2 => ¬ τof P = .std),
                  (d4CandFactor τof ê (α P.1) (P, 0)
                    * d4CandFactor τof ê
                        (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)) := by
          intro α
          calc (∏ P : LayerColumn 2,
                (d4CandFactor τof ê (α P.1) (P, 0)
                  * d4CandFactor τof ê
                      (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)))
              = (∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => τof P = .std),
                  (d4CandFactor τof ê (α P.1) (P, 0)
                    * d4CandFactor τof ê
                        (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)))
                * ∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => ¬ τof P = .std),
                    (d4CandFactor τof ê (α P.1) (P, 0)
                      * d4CandFactor τof ê
                          (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)) :=
                  (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
            _ = (∏ P : D4StdCol τof,
                  (d4CandFactor τof ê (α P.1.1) (P.1, 0)
                    * d4CandFactor τof ê
                        (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1)))
                * ∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => ¬ τof P = .std),
                    (d4CandFactor τof ê (α P.1) (P, 0)
                      * d4CandFactor τof ê
                          (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)) := by
                  congr 1
                  exact Finset.prod_subtype _
                    (fun x => Finset.mem_filter.trans
                      (and_iff_right (Finset.mem_univ x))) _
        have hd : ∀ α : LayerSite 2 → DihedralGroup 4,
            (∏ P : LayerColumn 2, d4Data τof u u' ê P)
            = (∏ P : D4StdCol τof, d4Data τof u u' ê P.1)
              * ∏ P ∈ Finset.univ.filter
                  (fun P : LayerColumn 2 => ¬ τof P = .std),
                  d4Data τof u u' ê P := by
          intro α
          calc (∏ P : LayerColumn 2, d4Data τof u u' ê P)
              = (∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => τof P = .std),
                  d4Data τof u u' ê P)
                * ∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => ¬ τof P = .std),
                    d4Data τof u u' ê P :=
                  (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
            _ = (∏ P : D4StdCol τof, d4Data τof u u' ê P.1)
                * ∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => ¬ τof P = .std),
                    d4Data τof u u' ê P := by
                  congr 1
                  exact Finset.prod_subtype _
                    (fun x => Finset.mem_filter.trans
                      (and_iff_right (Finset.mem_univ x))) _
        have hper : ∀ α : LayerSite 2 → DihedralGroup 4,
            (∏ P : D4StdCol τof,
              ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
              * d4Data τof u u' ê P.1))
            * ∏ P ∈ Finset.univ.filter
                (fun P : LayerColumn 2 => ¬ τof P = .std),
                d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α)
            = (∏ P : LayerColumn 2,
                (d4CandFactor τof ê (α P.1) (P, 0)
                  * d4CandFactor τof ê
                      (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)))
              * ∏ P : LayerColumn 2, d4Data τof u u' ê P := by
          intro α
          rw [d4_sign_prod_split τof u u' α ê, Finset.prod_mul_distrib,
            hf α, hd α]
          ring
        calc (∑ α : LayerSite 2 → DihedralGroup 4,
            (∏ P : D4StdCol τof,
              ((d4CandFactor τof ê (α P.1.1) (P.1, 0)
                * d4CandFactor τof ê
                    (α (layerShift P.1.2.1 P.1.2.2 P.1.1)) (P.1, 1))
              * d4Data τof u u' ê P.1))
            * ∏ P ∈ Finset.univ.filter
                (fun P : LayerColumn 2 => ¬ τof P = .std),
                d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
            = ∑ α : LayerSite 2 → DihedralGroup 4,
                (∏ P : LayerColumn 2,
                  (d4CandFactor τof ê (α P.1) (P, 0)
                    * d4CandFactor τof ê
                        (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)))
                * ∏ P : LayerColumn 2, d4Data τof u u' ê P :=
              Finset.sum_congr rfl fun α _ => hper α
          _ = (∏ P : LayerColumn 2, d4Data τof u u' ê P)
                * ∑ α : LayerSite 2 → DihedralGroup 4,
                    ∏ P : LayerColumn 2,
                      (d4CandFactor τof ê (α P.1) (P, 0)
                        * d4CandFactor τof ê
                            (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro α _
              ring
    _ = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          (∏ P : LayerColumn 2, d4Data τof u u' ê P)
          * ∏ c : LayerSite 2, ∑ a : DihedralGroup 4,
              ((d4CandList c).map (d4CandFactor τof ê a)).prod := by
        apply Finset.sum_congr rfl; intro ê _
        congr 1
        calc (∑ α : LayerSite 2 → DihedralGroup 4,
              ∏ P : LayerColumn 2,
                (d4CandFactor τof ê (α P.1) (P, 0)
                  * d4CandFactor τof ê
                      (α (layerShift P.2.1 P.2.2 P.1)) (P, 1)))
            = ∑ α : LayerSite 2 → DihedralGroup 4,
                ∏ c : LayerSite 2,
                  ((∏ P ∈ Finset.univ.filter
                      (fun P : LayerColumn 2 => P.1 = c),
                      d4CandFactor τof ê (α c) (P, 0))
                    * ∏ P ∈ Finset.univ.filter
                        (fun P : LayerColumn 2 =>
                          layerShift P.2.1 P.2.2 P.1 = c),
                        d4CandFactor τof ê (α c) (P, 1)) := by
              apply Finset.sum_congr rfl; intro α _
              exact d4_site_regroup α
                (fun P a => d4CandFactor τof ê a (P, 0))
                (fun P a => d4CandFactor τof ê a (P, 1))
          _ = ∏ c : LayerSite 2, ∑ a : DihedralGroup 4,
                ((∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => P.1 = c),
                    d4CandFactor τof ê a (P, 0))
                  * ∏ P ∈ Finset.univ.filter
                      (fun P : LayerColumn 2 =>
                        layerShift P.2.1 P.2.2 P.1 = c),
                      d4CandFactor τof ê a (P, 1)) :=
              d4_sum_prod_factor (F := fun c a =>
                (∏ P ∈ Finset.univ.filter
                    (fun P : LayerColumn 2 => P.1 = c),
                    d4CandFactor τof ê a (P, 0))
                  * ∏ P ∈ Finset.univ.filter
                      (fun P : LayerColumn 2 =>
                        layerShift P.2.1 P.2.2 P.1 = c),
                      d4CandFactor τof ê a (P, 1))
          _ = ∏ c : LayerSite 2, ∑ a : DihedralGroup 4,
                ((d4CandList c).map (d4CandFactor τof ê a)).prod := by
              apply Finset.prod_congr rfl; intro c _
              apply Finset.sum_congr rfl; intro a _
              exact d4_bracket_eq τof ê a c
    _ = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          (∏ P : LayerColumn 2, d4Data τof u u' ê P)
          * ∏ c : LayerSite 2,
              ∑ bs : Fin (d4PairCount τof c) → Fin 4,
                d4SiteCoeff (d4CandKlein τof (d4CandList c))
                    (List.ofFn bs)
                  * d4SitePF (List.ofFn bs)
                      (d4CandPairs τof ê (d4CandList c))
                  * d4SiteQF (List.ofFn bs)
                      (d4CandPairs τof ê (d4CandList c)) := by
        apply Finset.sum_congr rfl; intro ê _
        congr 1
        apply Finset.prod_congr rfl; intro c _
        exact d4_site_sum τof ê c
    _ = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
          ∑ κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4,
            (∏ P : LayerColumn 2, d4Data τof u u' ê P)
            * ∏ c : LayerSite 2,
                (d4SiteCoeff (d4CandKlein τof (d4CandList c))
                    (List.ofFn (κ c))
                  * d4SitePF (List.ofFn (κ c))
                      (d4CandPairs τof ê (d4CandList c))
                  * d4SiteQF (List.ofFn (κ c))
                      (d4CandPairs τof ê (d4CandList c))) := by
        apply Finset.sum_congr rfl; intro ê _
        rw [Fintype.prod_sum
          (fun (c : LayerSite 2)
            (bs : Fin (d4PairCount τof c) → Fin 4) =>
            d4SiteCoeff (d4CandKlein τof (d4CandList c))
                (List.ofFn bs)
              * d4SitePF (List.ofFn bs)
                  (d4CandPairs τof ê (d4CandList c))
              * d4SiteQF (List.ofFn bs)
                  (d4CandPairs τof ê (d4CandList c))),
          Finset.mul_sum]
    _ = ∑ κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4,
          ∑ ê : D4Slot τof → Fin 2 × Fin 2,
            (∏ P : LayerColumn 2, d4Data τof u u' ê P)
            * ∏ c : LayerSite 2,
                (d4SiteCoeff (d4CandKlein τof (d4CandList c))
                    (List.ofFn (κ c))
                  * d4SitePF (List.ofFn (κ c))
                      (d4CandPairs τof ê (d4CandList c))
                  * d4SiteQF (List.ofFn (κ c))
                      (d4CandPairs τof ê (d4CandList c))) :=
        Finset.sum_comm
    _ = ∑ κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4,
          (∏ c : LayerSite 2,
            d4SiteCoeff (d4CandKlein τof (d4CandList c))
              (List.ofFn (κ c)))
          * ∑ ê : D4Slot τof → Fin 2 × Fin 2,
              ((∏ P : LayerColumn 2, d4Data τof u u' ê P)
                * ∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                    (d4CandPairs τof ê (d4CandList c)))
                * ∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                    (d4CandPairs τof ê (d4CandList c)) := by
        apply Finset.sum_congr rfl; intro κ _
        have hT : ∀ ê : D4Slot τof → Fin 2 × Fin 2,
            (∏ c : LayerSite 2,
              (d4SiteCoeff (d4CandKlein τof (d4CandList c))
                  (List.ofFn (κ c))
                * d4SitePF (List.ofFn (κ c))
                    (d4CandPairs τof ê (d4CandList c))
                * d4SiteQF (List.ofFn (κ c))
                    (d4CandPairs τof ê (d4CandList c))))
            = (∏ c : LayerSite 2,
                d4SiteCoeff (d4CandKlein τof (d4CandList c))
                  (List.ofFn (κ c)))
              * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                  (d4CandPairs τof ê (d4CandList c)))
              * ∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                  (d4CandPairs τof ê (d4CandList c)) := by
          intro ê
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        calc (∑ ê : D4Slot τof → Fin 2 × Fin 2,
              (∏ P : LayerColumn 2, d4Data τof u u' ê P)
              * ∏ c : LayerSite 2,
                  (d4SiteCoeff (d4CandKlein τof (d4CandList c))
                      (List.ofFn (κ c))
                    * d4SitePF (List.ofFn (κ c))
                        (d4CandPairs τof ê (d4CandList c))
                    * d4SiteQF (List.ofFn (κ c))
                        (d4CandPairs τof ê (d4CandList c))))
            = ∑ ê : D4Slot τof → Fin 2 × Fin 2,
                (∏ c : LayerSite 2,
                  d4SiteCoeff (d4CandKlein τof (d4CandList c))
                    (List.ofFn (κ c)))
                * ((∏ P : LayerColumn 2, d4Data τof u u' ê P)
                  * (∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                      (d4CandPairs τof ê (d4CandList c)))
                  * ∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                      (d4CandPairs τof ê (d4CandList c))) := by
              apply Finset.sum_congr rfl; intro ê _
              rw [hT ê]; ring
          _ = (∏ c : LayerSite 2,
                d4SiteCoeff (d4CandKlein τof (d4CandList c))
                  (List.ofFn (κ c)))
              * ∑ ê : D4Slot τof → Fin 2 × Fin 2,
                  ((∏ P : LayerColumn 2, d4Data τof u u' ê P)
                    * ∏ c : LayerSite 2, d4SitePF (List.ofFn (κ c))
                        (d4CandPairs τof ê (d4CandList c)))
                    * ∏ c : LayerSite 2, d4SiteQF (List.ofFn (κ c))
                        (d4CandPairs τof ê (d4CandList c)) := by
              rw [Finset.mul_sum]
    _ = ∑ κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4,
          ((d4Weight τof κ : ℝ) : ℂ)
          * (d4Phi τof (fun c => List.ofFn (κ c)) u
            * d4Psi τof (fun c => List.ofFn (κ c)) u') := by
        apply Finset.sum_congr rfl; intro κ _
        rw [d4_coeff_prod_eq, d4_ends_factor τof κ u u']
    _ = ∑ κ : ∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4,
          d4Feat τof κ u * star (d4Feat τof κ u') := by
        apply Finset.sum_congr rfl; intro κ _
        have hw : ((Real.sqrt (d4Weight τof κ) : ℂ))
            * ((Real.sqrt (d4Weight τof κ) : ℂ))
            = ((d4Weight τof κ : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← pow_two,
            Real.sq_sqrt (d4Weight_nonneg τof κ)]
        have hstar : star ((Real.sqrt (d4Weight τof κ) : ℂ))
            = ((Real.sqrt (d4Weight τof κ) : ℂ)) := by simp
        show ((d4Weight τof κ : ℝ) : ℂ)
            * (d4Phi τof (fun c => List.ofFn (κ c)) u
              * d4Psi τof (fun c => List.ofFn (κ c)) u')
          = ((Real.sqrt (d4Weight τof κ) : ℂ))
              * d4Phi τof (fun c => List.ofFn (κ c)) u
            * star (((Real.sqrt (d4Weight τof κ) : ℂ))
              * d4Phi τof (fun c => List.ofFn (κ c)) u')
        rw [d4Psi_eq_phi, star_mul, d4Phi_star, hstar, ← hw]; ring

/-- **(SEP, discharged in scratch)** Every type assignment
at the seat separates.  In the module this proof replaces
the brick-3 sorry at `d4_separation`, whose frozen
statement is identical. -/
theorem d4_separation_proof (τof : LayerColumn 2 → D4Type) :
    D4Separated τof :=
  ⟨∀ c : LayerSite 2, Fin (d4PairCount τof c) → Fin 4, inferInstance,
    d4Feat τof, fun u u' => d4_stratum_gram τof u u'⟩

/-- **(SEP, PIN)** Every type assignment at the seat
separates.  This is the scoping's (PIN-F) at the D₄ seat;
its proof is the L4–L10 assembly of §§A–E (brick 3, on the
§§A–C lemmas landed in brick 2 and the L7 pin below). -/
theorem d4_separation (τof : LayerColumn 2 → D4Type) :
    D4Separated τof :=
  d4_separation_proof τof

/-- **(Assembly, PIN)** The separation identities assemble
the gap: given SEP for every type assignment, the kernel is
the Gram sum of the gap, with the landed weights
`gramColWeight (d4Coeff β) ·` — the L1–L3 + L10 calc of
brick 3. -/
theorem d4KernelEqGap_of_separation
    (hsep : ∀ τof : LayerColumn 2 → D4Type, D4Separated τof) :
    ∀ β : ℝ, 0 ≤ β → d4KernelEqGap β := by
  intro β _hβ
  have key : ∀ τof : LayerColumn 2 → D4Type,
      ∃ (κ : Type) (hκ : Fintype κ)
        (feat : κ → (LayerLink 2 → DihedralGroup 4) → ℂ),
        ∀ u u' : LayerLink 2 → DihedralGroup 4,
          (∑ α : LayerSite 2 → DihedralGroup 4,
              ∏ P : LayerColumn 2,
                d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α))
            = ∑ k, feat k u * star (feat k u') := hsep
  choose κ hκ feat hfeat using key
  haveI : ∀ τof : LayerColumn 2 → D4Type, Fintype (κ τof) := hκ
  -- The chosen `Fintype (κ τof)` and the ambient instance are
  -- equal (`Fintype` is a subsingleton); transport the finite
  -- sum's index set across that equality (the probe's maneuver
  -- in `layerKernelPos_of_d4KernelEqGap`).
  have hunivκ : ∀ τof : LayerColumn 2 → D4Type,
      @Finset.univ (κ τof) (hκ τof) = Finset.univ := fun τof =>
    congrArg (fun I : Fintype (κ τof) => @Finset.univ (κ τof) I)
      (Subsingleton.elim _ _)
  -- The stratum normalization: `layerKernel_d4_eq_sum` carries
  -- the factor `(card)⁻¹` against the raw stratum sum that SEP
  -- is pinned in; the assembly absorbs it into the features
  -- through the real square root `c`, `c * c = (card)⁻¹`.
  have hcard : (0 : ℝ) ≤ ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  set c : ℝ := Real.sqrt ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹ with hc
  have hc2 : (c : ℂ) * (c : ℂ)
      = ((((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, hc, Real.sq_sqrt hcard]
  refine ⟨Σ τof : LayerColumn 2 → D4Type, κ τof, inferInstance,
    fun j => j.1, fun j u => (c : ℂ) * feat j.1 j.2 u, fun u u' => ?_⟩
  have hcol : ∀ α : LayerSite 2 → DihedralGroup 4,
      ((Real.exp (-(layerAction nbRep β α u u')) : ℝ) : ℂ)
        = ∏ P : LayerColumn 2, ((Real.exp (-β * gramDens nbRep
            (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ) := by
    intro α
    rw [d4_layerAction_sum_columns, Real.exp_sum, Complex.ofReal_prod]
  have hsplit : ∀ (τof : LayerColumn 2 → D4Type)
      (α : LayerSite 2 → DihedralGroup 4),
      ∏ P : LayerColumn 2, ((d4Coeff β (τof P) : ℝ) : ℂ)
          * d4Char (τof P) (colWord u u' P.1 P.2.1 P.2.2 α)
        = ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
          * ∏ P : LayerColumn 2, d4Char (τof P)
              (colWord u u' P.1 P.2.1 P.2.2 α) := by
    intro τof α
    rw [Finset.prod_mul_distrib]
    congr 1
    exact (Complex.ofReal_prod _ _).symm
  calc layerKernel nbμG nbRep β u u'
      = ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹
          • ∑ α, ∏ P : LayerColumn 2,
              ((Real.exp (-β * gramDens nbRep
                (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ) := by
        rw [layerKernel_d4_eq_sum]
        congr 1
        exact Finset.sum_congr rfl fun α _ => hcol α
    _ = ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹
          • ∑ τof : LayerColumn 2 → D4Type, ∑ α,
              ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                * ∏ P : LayerColumn 2, d4Char (τof P)
                    (colWord u u' P.1 P.2.1 P.2.2 α) := by
        congr 1
        calc ∑ α, ∏ P : LayerColumn 2,
                ((Real.exp (-β * gramDens nbRep
                  (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ)
            = ∑ α, ∑ τof : LayerColumn 2 → D4Type,
                ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                  * ∏ P : LayerColumn 2, d4Char (τof P)
                      (colWord u u' P.1 P.2.1 P.2.2 α) := by
              refine Finset.sum_congr rfl fun α _ => ?_
              calc ∏ P : LayerColumn 2,
                      ((Real.exp (-β * gramDens nbRep
                        (colWord u u' P.1 P.2.1 P.2.2 α)) : ℝ) : ℂ)
                  = ∏ P : LayerColumn 2, ∑ τ : D4Type,
                        ((d4Coeff β τ : ℝ) : ℂ)
                          * d4Char τ (colWord u u' P.1 P.2.1 P.2.2 α) :=
                      Finset.prod_congr rfl fun P _ => d4_expansion β _
                _ = ∑ τof : LayerColumn 2 → D4Type, ∏ P : LayerColumn 2,
                        ((d4Coeff β (τof P) : ℝ) : ℂ)
                          * d4Char (τof P)
                              (colWord u u' P.1 P.2.1 P.2.2 α) :=
                      Fintype.prod_sum _
                _ = ∑ τof : LayerColumn 2 → D4Type,
                        ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                          * ∏ P : LayerColumn 2, d4Char (τof P)
                              (colWord u u' P.1 P.2.1 P.2.2 α) :=
                      Finset.sum_congr rfl fun τof _ => hsplit τof α
          _ = ∑ τof : LayerColumn 2 → D4Type, ∑ α,
                ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                  * ∏ P : LayerColumn 2, d4Char (τof P)
                      (colWord u u' P.1 P.2.1 P.2.2 α) :=
              Finset.sum_comm
    _ = ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹
          • ∑ τof : LayerColumn 2 → D4Type,
              ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                * ∑ α, ∏ P : LayerColumn 2, d4Char (τof P)
                    (colWord u u' P.1 P.2.1 P.2.2 α) := by
        congr 1
        refine Finset.sum_congr rfl fun τof _ => ?_
        rw [Finset.mul_sum]
    _ = ((Fintype.card (LayerSite 2 → DihedralGroup 4) : ℝ))⁻¹
          • ∑ τof : LayerColumn 2 → D4Type,
              ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                * ∑ k, feat τof k u * star (feat τof k u') := by
        have hS : (∑ τof : LayerColumn 2 → D4Type,
              ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                * ∑ α, ∏ P : LayerColumn 2, d4Char (τof P)
                    (colWord u u' P.1 P.2.1 P.2.2 α))
            = ∑ τof : LayerColumn 2 → D4Type,
              ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ)
                * ∑ k, feat τof k u * star (feat τof k u') :=
          Finset.sum_congr rfl fun τof _ => by
            rw [hfeat τof u u', hunivκ τof]
        rw [hS]
    _ = ∑ j : Σ τof : LayerColumn 2 → D4Type, κ τof,
          ((gramColWeight (d4Coeff β) (fun j => j.1) j : ℝ) : ℂ)
            * ((c : ℂ) * feat j.1 j.2 u)
            * star ((c : ℂ) * feat j.1 j.2 u') := by
        have hsig : ∀ F : (Σ τof : LayerColumn 2 → D4Type, κ τof) → ℂ,
            ∑ j, F j = ∑ τof, ∑ k, F ⟨τof, k⟩ := by
          intro F
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        rw [hsig, Complex.real_smul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τof _ => ?_
        rw [← mul_assoc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hw : ((gramColWeight (d4Coeff β) (fun j => j.1)
              (⟨τof, k⟩ : Σ τof : LayerColumn 2 → D4Type, κ τof) : ℝ) : ℂ)
            = ((gramColWeight (d4Coeff β) (fun τ => τ) τof : ℝ) : ℂ) := rfl
        have hstar : star ((c : ℂ) * feat τof k u')
            = (c : ℂ) * star (feat τof k u') := by
          have hsc : star (c : ℂ) = (c : ℂ) := by simp
          rw [star_mul, hsc, mul_comm]
        rw [hw, hstar, ← hc2]
        ring

/-- **(L12)** The gap at every `β ≥ 0` — proved from the two
pins `(SEP)` and `(Assembly)`; T1 exactly when they are. -/
theorem d4KernelEqGap_all : ∀ β : ℝ, 0 ≤ β → d4KernelEqGap β :=
  d4KernelEqGap_of_separation d4_separation

/-- **(L12, corollary)** The pinned D₄ instance
`layerKernelPosD4Std`, by the probe's landed reduction. -/
theorem layerKernelPosD4Std_holds : layerKernelPosD4Std :=
  layerKernelPosD4Std_of_gaps d4KernelEqGap_all

/-! ## §F. The L11 degeneracy check (F3)

The scoping's F3 test: K-GRAM-DEGEN fires iff every certificate
at the seat has constant features (`gramFeaturesConstant`).  The
test is decidable on one explicit pattern: the constant pattern
`τof ≡ sgnA`.  Its stratum sum separates in closed form
(`d4_all_sgnA_stratum`): at every site the outgoing `sgnA`
characters and the incoming `sgnA` characters cancel in pairs
under the stratum product (the involution argument below), so
the pattern's kernel is the stratum cardinality times a single
explicit feature — the product of the `sgnA` characters of all
column links — times itself.  That feature is nonconstant: it
is `1` at the identity configuration and `-1` after flipping
one link to `r 1` (the fiber of `layerLinkOf` over any link is
a single column, `layerLinkOf_inj_column`).  Hence the
pattern's separated kernel is a nonconstant function of
`(u, u')`, so NO constant feature family separates it
(`d4_degeneracy_check`); in particular the assembled
certificate of `d4KernelEqGap_of_separation`, whose
`(≡ sgnA)`-slice separates this pattern once SEP lands, does
not have the `gramFeaturesConstant` shape.  **Verdict:
K-GRAM-DEGEN does not fire.**  (The scoping's parenthetical
witness was a two-`std` pattern; the all-`sgnA` pattern is a
cleaner witness of the same F3 content, and it is the one
decidable in closed form.) -/

/-- The `sgnA` character takes values in `{1, −1}` (finite
check on the 8 group elements; the `ZMod 4` value facts are
the brick-2 ones, `decide` only on `ZMod 4`). -/
theorem d4Char_sgnA_mem (g : DihedralGroup 4) :
    d4Char .sgnA g = 1 ∨ d4Char .sgnA g = -1 := by
  have hv0 : (0 : ZMod 4).val = 0 := by decide
  have hv1 : (1 : ZMod 4).val = 1 := by decide
  have hv2 : (2 : ZMod 4).val = 2 := by decide
  have hv3 : (3 : ZMod 4).val = 3 := by decide
  have hv : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    decide
  cases g with
  | r i =>
    rcases hv i with rfl | rfl | rfl | rfl <;>
      simp [d4Char, d4SignChar, hv0, hv1, hv2, hv3] <;> norm_num
  | sr i =>
    rcases hv i with rfl | rfl | rfl | rfl <;>
      simp [d4Char, d4SignChar, hv0, hv1, hv2, hv3] <;> norm_num

theorem d4Char_sgnA_inv_val (g : DihedralGroup 4) :
    (d4Char .sgnA g)⁻¹ = d4Char .sgnA g := by
  rcases d4Char_sgnA_mem g with h | h <;> simp [h]

theorem d4Char_sgnA_star (g : DihedralGroup 4) :
    star (d4Char .sgnA g) = d4Char .sgnA g := by
  rcases d4Char_sgnA_mem g with h | h <;> simp [h]

theorem d4Char_sgnA_ne_zero (g : DihedralGroup 4) :
    d4Char .sgnA g ≠ 0 := by
  rcases d4Char_sgnA_mem g with h | h <;> simp [h]

theorem d4Char_sgnA_one : d4Char .sgnA 1 = 1 := by
  have h1 : (1 : DihedralGroup 4) = .r 0 := rfl
  rw [h1]
  simp [d4Char, d4SignChar]

theorem d4Char_sgnA_r_one : d4Char .sgnA (.r (1 : ZMod 4)) = -1 := by
  have hv1 : (1 : ZMod 4).val = 1 := by decide
  simp [d4Char, d4SignChar, hv1]

/-- The character of an inverse is the inverse of the
character, for `sgnA` (from `d4Char_sign_mul` at `g * g⁻¹`). -/
theorem d4Char_sgnA_inv_apply (g : DihedralGroup 4) :
    d4Char .sgnA g⁻¹ = (d4Char .sgnA g)⁻¹ := by
  have h1 : d4Char .sgnA g⁻¹ * d4Char .sgnA g = 1 := by
    have h := d4Char_sign_mul .sgnA (Or.inr (Or.inl rfl)) g⁻¹ g
    rw [inv_mul_cancel, d4Char_sgnA_one] at h
    exact h.symm
  exact eq_inv_of_mul_eq_one_left h1

/-- The single feature separating the constant `sgnA`
pattern: the product of the `sgnA` characters of all column
links. -/
noncomputable def d4SignFeature (u : LayerLink 2 → DihedralGroup 4) :
    ℂ :=
  ∏ P : LayerColumn 2,
    d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2))

theorem d4SignFeature_star (u : LayerLink 2 → DihedralGroup 4) :
    star (d4SignFeature u) = d4SignFeature u := by
  rw [d4SignFeature, star_prod]
  exact Finset.prod_congr rfl fun P _ => d4Char_sgnA_star _

theorem d4SignFeature_one :
    d4SignFeature (1 : LayerLink 2 → DihedralGroup 4) = 1 := by
  simp [d4SignFeature, d4Char_sgnA_one]

-- `layerShift_two_involutive` is stated before §G above
-- (brick 4): §G's filter lemmas consume it.  Its §F
-- siblings are unaffected.

/-- At `N = 2` the layer shift has no fixed site (it adds `1`
at the `ν` coordinate, and `1 ≠ 0` in `ZMod 2`). -/
theorem layerShift_two_ne_self (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite 2) : layerShift ν hν c ≠ c := by
  intro h
  have hcoord : (torusShift 2 ν c.1) ν = c.1 ν :=
    congrFun (congrArg Subtype.val h) ν
  rw [torusShift_apply_coord, Pi.single_eq_same] at hcoord
  have key : (1 : ZMod 2) + c.1 ν = (0 : ZMod 2) + c.1 ν := by
    rw [zero_add]; exact hcoord
  have h10 : (1 : ZMod 2) = 0 := add_right_cancel_iff.mp key
  exact (by decide : (1 : ZMod 2) ≠ 0) h10

/-- The column shift `P ↦ (layerShift P.2 P.1, P.2)`. -/
def d4ColShift (P : LayerColumn 2) : LayerColumn 2 :=
  ⟨layerShift P.2.1 P.2.2 P.1, P.2⟩

theorem d4ColShift_involutive (P : LayerColumn 2) :
    d4ColShift (d4ColShift P) = P := by
  obtain ⟨c, ⟨ν, hν⟩⟩ := P
  show (⟨layerShift ν hν (layerShift ν hν c), ⟨ν, hν⟩⟩ :
      LayerColumn 2) = ⟨c, ⟨ν, hν⟩⟩
  rw [layerShift_two_involutive]

theorem d4ColShift_ne (P : LayerColumn 2) : d4ColShift P ≠ P := by
  obtain ⟨c, ⟨ν, hν⟩⟩ := P
  intro h
  have h1 : layerShift ν hν c = c :=
    congrArg (fun P : LayerColumn 2 => P.1) h
  exact layerShift_two_ne_self ν hν c h1

/-- The fiber of `layerLinkOf` over any layer link contains
at most one column: the link's value `(c.1, ν)` determines
the column. -/
theorem layerLinkOf_inj_column (P Q : LayerColumn 2)
    (h : layerLinkOf P.1 P.2.1 P.2.2
      = layerLinkOf Q.1 Q.2.1 Q.2.2) : P = Q := by
  obtain ⟨⟨c₁, hc₁⟩, ⟨ν₁, hν₁⟩⟩ := P
  obtain ⟨⟨c₂, hc₂⟩, ⟨ν₂, hν₂⟩⟩ := Q
  have h2 : (c₁, ν₁) = (c₂, ν₂) := congrArg Subtype.val h
  rw [Prod.ext_iff] at h2
  obtain ⟨h1, hν⟩ := h2
  subst h1
  subst hν
  rfl

/-- A concrete base column for the L11 witness. -/
def d4BaseColumn : LayerColumn 2 :=
  ⟨⟨fun _ => 0, by decide⟩, ⟨1, by decide⟩⟩

/-- The feature flips sign when the base column's link is set
to `r 1`: every other column's link stays `1` (the fiber is a
single column), and `sgnA (r 1) = -1`. -/
theorem d4SignFeature_flip :
    d4SignFeature (Function.update (1 : LayerLink 2 → DihedralGroup 4)
      (layerLinkOf d4BaseColumn.1 d4BaseColumn.2.1 d4BaseColumn.2.2)
      (.r 1)) = -1 := by
  rw [d4SignFeature]
  refine (Finset.prod_eq_single d4BaseColumn ?_ ?_).trans ?_
  · intro P _ hP
    rw [Function.update_of_ne
      (fun hh => hP (layerLinkOf_inj_column P d4BaseColumn hh)) _ _]
    simp [d4Char_sgnA_one]
  · intro hmem
    exact absurd (Finset.mem_univ d4BaseColumn) hmem
  · rw [Function.update_self, d4Char_sgnA_r_one]

/-- **The constant `sgnA` pattern separates in closed form**:
its stratum sum is the stratum cardinality times the explicit
feature times itself.  The `α`-dependent factors cancel in
pairs under the column involution `P ↦ (shift P.1, P.2)`
(`Finset.prod_ninvolution`: the factor at `P` times the factor
at the shifted column is `χ(α P.1) · χ(α (σ P))⁻¹ ·
χ(α (σ P)) · χ(α P.1)⁻¹ = 1`, the shift is fixed-point-free
and involutive at `N = 2`). -/
theorem d4_all_sgnA_stratum (u u' : LayerLink 2 → DihedralGroup 4) :
    (∑ α : LayerSite 2 → DihedralGroup 4,
      ∏ P : LayerColumn 2,
        d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α))
      = (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)
        * d4SignFeature u * d4SignFeature u' := by
  have hfactor : ∀ (α : LayerSite 2 → DihedralGroup 4)
      (P : LayerColumn 2),
      d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α)
        = (d4Char .sgnA (α P.1)
            * (d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))⁻¹)
          * (d4Char .sgnA (u' (layerLinkOf P.1 P.2.1 P.2.2))
            * (d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2)))⁻¹) := by
    intro α P
    have hm := d4Char_sign_mul .sgnA (Or.inr (Or.inl rfl))
    show d4Char .sgnA (α P.1 * u' (layerLinkOf P.1 P.2.1 P.2.2)
        * (α (layerShift P.2.1 P.2.2 P.1))⁻¹
        * (u (layerLinkOf P.1 P.2.1 P.2.2))⁻¹) = _
    rw [hm, hm, hm, d4Char_sgnA_inv_apply, d4Char_sgnA_inv_apply]
    ring
  have halpha : ∀ α : LayerSite 2 → DihedralGroup 4,
      ∏ P : LayerColumn 2, (d4Char .sgnA (α P.1)
          * (d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))⁻¹)
        = 1 := by
    intro α
    have hfinv : ∀ P : LayerColumn 2,
        d4Char .sgnA (α (d4ColShift P).1)
          * (d4Char .sgnA (α (layerShift (d4ColShift P).2.1
              (d4ColShift P).2.2 (d4ColShift P).1)))⁻¹
          = d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1))
            * (d4Char .sgnA (α P.1))⁻¹ := by
      intro P
      show d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1))
          * (d4Char .sgnA
            (α (layerShift P.2.1 P.2.2
              (layerShift P.2.1 P.2.2 P.1))))⁻¹ = _
      rw [layerShift_two_involutive]
    refine Finset.prod_ninvolution d4ColShift ?_ ?_
      (fun P => Finset.mem_univ _) d4ColShift_involutive
    · intro P
      rw [hfinv P]
      calc (d4Char .sgnA (α P.1)
            * (d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))⁻¹)
          * (d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1))
            * (d4Char .sgnA (α P.1))⁻¹)
          = d4Char .sgnA (α P.1)
            * ((d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))⁻¹
              * d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))
            * (d4Char .sgnA (α P.1))⁻¹ := by ring
        _ = d4Char .sgnA (α P.1) * (d4Char .sgnA (α P.1))⁻¹ := by
          rw [inv_mul_cancel₀ (d4Char_sgnA_ne_zero _), mul_one]
        _ = 1 := mul_inv_cancel₀ (d4Char_sgnA_ne_zero _)
    · intro P _
      exact d4ColShift_ne P
  have hprod : ∀ α : LayerSite 2 → DihedralGroup 4,
      ∏ P : LayerColumn 2,
          d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α)
        = d4SignFeature u * d4SignFeature u' := by
    intro α
    calc ∏ P : LayerColumn 2,
            d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α)
        = ∏ P : LayerColumn 2,
            ((d4Char .sgnA (α P.1)
              * (d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))⁻¹)
            * (d4Char .sgnA (u' (layerLinkOf P.1 P.2.1 P.2.2))
              * (d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2)))⁻¹)) :=
          Finset.prod_congr rfl fun P _ => hfactor α P
      _ = (∏ P : LayerColumn 2, (d4Char .sgnA (α P.1)
              * (d4Char .sgnA (α (layerShift P.2.1 P.2.2 P.1)))⁻¹))
            * ∏ P : LayerColumn 2,
              (d4Char .sgnA (u' (layerLinkOf P.1 P.2.1 P.2.2))
              * (d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2)))⁻¹) :=
          Finset.prod_mul_distrib
      _ = 1 * ((∏ P : LayerColumn 2,
              d4Char .sgnA (u' (layerLinkOf P.1 P.2.1 P.2.2)))
            * ∏ P : LayerColumn 2,
              (d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2)))⁻¹) := by
          rw [halpha α, Finset.prod_mul_distrib]
      _ = d4SignFeature u' * d4SignFeature u := by
          have h2 : (∏ P : LayerColumn 2,
              (d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2)))⁻¹)
              = ∏ P : LayerColumn 2,
                d4Char .sgnA (u (layerLinkOf P.1 P.2.1 P.2.2)) :=
            Finset.prod_congr rfl fun P _ => d4Char_sgnA_inv_val _
          simp only [one_mul, h2, d4SignFeature]
      _ = d4SignFeature u * d4SignFeature u' := mul_comm _ _
  calc (∑ α : LayerSite 2 → DihedralGroup 4,
        ∏ P : LayerColumn 2,
          d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α))
      = ∑ _α : LayerSite 2 → DihedralGroup 4,
          (d4SignFeature u * d4SignFeature u') :=
        Finset.sum_congr rfl fun α _ => hprod α
    _ = (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)
          * (d4SignFeature u * d4SignFeature u') := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)
          * d4SignFeature u * d4SignFeature u' := by ring

/-- **(L11) The degeneracy check, F3 form.**  Any feature
family separating the constant `sgnA` pattern has a
nonconstant feature: were all features constant, the
separated kernel would be constant in `(u, u')`, but
`d4_all_sgnA_stratum` evaluates it to `card` at
`(1, 1)` and to `-card` at `(1, flip)`, and `card ≠ 0`.
So the assembled certificate does not have the
`gramFeaturesConstant` shape — **K-GRAM-DEGEN does not
fire**. -/
theorem d4_degeneracy_check {κ : Type} [Fintype κ]
    (feat : κ → (LayerLink 2 → DihedralGroup 4) → ℂ)
    (hsep : ∀ u u' : LayerLink 2 → DihedralGroup 4,
      (∑ α : LayerSite 2 → DihedralGroup 4,
        ∏ P : LayerColumn 2,
          d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α))
        = ∑ k, feat k u * star (feat k u')) :
    ∃ k u u', feat k u ≠ feat k u' := by
  by_contra hcon
  push Not at hcon
  set u₀ : LayerLink 2 → DihedralGroup 4 :=
    (1 : LayerLink 2 → DihedralGroup 4) with hu₀
  set u₁ : LayerLink 2 → DihedralGroup 4 := Function.update u₀
    (layerLinkOf d4BaseColumn.1 d4BaseColumn.2.1 d4BaseColumn.2.2)
    (.r 1) with hu₁
  have hK : ∀ u u' : LayerLink 2 → DihedralGroup 4,
      (∑ α : LayerSite 2 → DihedralGroup 4,
        ∏ P : LayerColumn 2,
          d4Char .sgnA (colWord u u' P.1 P.2.1 P.2.2 α))
        = ∑ k, feat k u₀ * star (feat k u₀) := by
    intro u u'
    rw [hsep u u']
    exact Finset.sum_congr rfl fun k _ => by
      rw [hcon k u u₀, hcon k u' u₀]
  have hcard : (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)
      ≠ 0 := by
    have hpos : 0 < Fintype.card (LayerSite 2 → DihedralGroup 4) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => (1 : DihedralGroup 4)⟩
    exact_mod_cast hpos.ne'
  have e1 := hK u₀ u₀
  have e2 := hK u₀ u₁
  rw [d4_all_sgnA_stratum] at e1 e2
  rw [hu₀, d4SignFeature_one] at e1
  rw [hu₁, hu₀, d4SignFeature_one, d4SignFeature_flip] at e2
  rw [mul_one, mul_one] at e1
  rw [mul_one] at e2
  have hceq : (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)
      = (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ) * -1 :=
    e1.trans e2.symm
  rw [mul_neg, mul_one] at hceq
  have h0 : (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)
      = 0 := by
    have h2 := congrArg
      (fun z : ℂ => z
        + (Fintype.card (LayerSite 2 → DihedralGroup 4) : ℂ)) hceq
    rw [neg_add_cancel, ← two_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  exact hcard h0

-- Axiom audit (final, brick 4): SEP is discharged (§G and
-- `d4_separation` above); the module carries zero sorries,
-- and both headlines print exactly the clean triple below:
-- [propext, Classical.choice, Quot.sound].
#print axioms d4KernelEqGap_all
#print axioms layerKernelPosD4Std_holds

end ThetLogos
