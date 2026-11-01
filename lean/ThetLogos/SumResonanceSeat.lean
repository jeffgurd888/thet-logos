import Mathlib.Tactic
import ThetLogos.SumResonance
import ThetLogos.SumResonanceCore
import ThetLogos.SumResonanceForcing
import ThetLogos.Q7C4R4Spectrum

/-!
# Sum resonance at the Q7CR composite seat (RES-4, with RES-4a)

Closing brick of the resonance line, per the coordinator pack
`routeb-general-scratch/pack-res-4.md` and the ratified scoping memo
`routeb-general-scratch/scoping-resonance-2026-10-30.md` (§4 and §6).
RES-0/1/2's vocabulary and theorems (`ThetLogos.SumResonance`,
`SumResonanceCore`, `SumResonanceForcing`) are cited, never forked.
RES-3's module (`SumResonanceRatios`) is NOT imported: as found in
the tree at this brick's Step 0 it is untracked and incomplete
(it ends in a `sorry` at its (b2) lemma), so the seat's ratio counts
below are proved directly from RES-0's `resCount` definition and
the seat's own tone form, not from RES-3.

## Step 0 inventory (what Q7CR-2 actually delivered)

`ThetLogos.Q7C4R4Spectrum` (Q7CR-2, BR1-012) delivers, over **ℝ**:
`s₇ : Fin 14 → ℝ`, `s₄ : Fin 8 → ℝ`, `s_R : Fin 4 → ℝ` (the factor
squares' eigenvalues, realified dimensions `14 / 8 / 4`), the
composite eigenvalue function `eigComp : compIndex → ℝ` on
`compIndex = ((Fin 7 × Fin 2) × (Fin 4 × Fin 2)) × Fin 4`, the
eigenbasis theorem `dirac_sq_basisComp_eig` (from the landed
`diracQ7C4R4_sq`), and the multiset `spectrumQ7CR2 : Multiset ℝ`
with card `448`, sum `2723`, second moment `1518111 / 64`.
It does **NOT** deliver the composite `D²` multiset spectrum in
the form `sumSpec3 s₇ s₄ s_R` over **ℚ** that §4 of the memo
registers: the delivered spectra are real, and the composite is
indexed by `compIndex`, not by `Fin 14 × Fin 8 × Fin 4`.
**RES-4a verdict: the bridge is needed, and it is built in §2
below** — ℚ factor families `s7Q s4Q sRQ` transcribed exactly from
the delivered factor data, cast lemmas identifying them with
`s₇ s₄ s_R`, and the multiset bridge
`(sumSpec3 s7Q s4Q sRQ).map (↑) = spectrumQ7CR2`.

## Face fences (§4, verbatim in substance)

The factor spectra at this seat are CHOSEN INPUTS (Q7CR-2's named
choices; any clock-data diagonal is entered measured data, T2/T4).
Seat resonances are properties of the choices. The abstract
theorems are the line's content; the seat is an exhibit of them,
unless a §3 forcing statement applies at the seat — then the
forcing theorem is the content. Any ratio among the seat's tones
coinciding with a measured value would be a Dial-1 NEW entry under
the relabeling rule — this line never makes that entry itself.
No Dial-1 entry is made by this line. NO CLAIM. Dials 0/4.

**K-RES-1 (pre-registered, §6) is evaluated in the BRIDGE-1 run
record and the coordinator report for this brick:** the seat's
pigeonhole floor is `448 − K_seat = 448 − 14 = 434`, the proved
excess is `434`, the difference is `0`; the (a3) attribution is
`(0,0,0) ↦ 13312`, the single pairwise face `(±4, 0, ∓4) ↦ 1024`
each, genuinely ternary `0`. See §6 below for the Lean forms.
-/

namespace ThetLogos

open Finset

/-! ## §1. The ℚ factor families (transcribed from Q7CR-2's delivered data)

The factor diagonals, over ℚ, in Q7CR-2's exact choices:
`a₇ = (3, -3, 2, -2, 1, -1, 0)` (CHOSEN), `d₄ = (-3/8, -1/8, 1/8, 3/8)`
(the centered Z4 ladder, T2 input with CHOSEN centering),
`r_R = (0, 2, -2, 0)` (CHOSEN). The ℚ factor-square families mirror
the delivered real definitions `s₇ s₄ s_R` construction-for-construction
(realification through `finProdFinEquiv`). -/

/-- The Q⁷ diagonal over ℚ (CHOSEN, Q7CR-2's named entries). -/
def a7Q : Fin 7 → ℚ := ![3, -3, 2, -2, 1, -1, 0]

/-- The C⁴ diagonal over ℚ (centered ladder, Q7CR-2's choice). -/
def d4Q : Fin 4 → ℚ := ![-3 / 8, -1 / 8, 1 / 8, 3 / 8]

/-- The R⁴ diagonal over ℚ (CHOSEN, Q7CR-2's named entries). -/
def rRQ : Fin 4 → ℚ := ![0, 2, -2, 0]

/-- The Q⁷ factor-square eigenvalues over ℚ (`Fin 14`, realified):
the ℚ mirror of the delivered `s₇`. -/
def s7Q : Fin 14 → ℚ :=
  fun i => a7Q ((finProdFinEquiv (m := 7) (n := 2)).symm i).1 ^ 2

/-- The C⁴ factor-square eigenvalues over ℚ (`Fin 8`, realified):
the ℚ mirror of the delivered `s₄`. -/
def s4Q : Fin 8 → ℚ :=
  fun i => d4Q ((finProdFinEquiv (m := 4) (n := 2)).symm i).1 ^ 2

/-- The R⁴ factor-square eigenvalues over ℚ (`Fin 4`):
the ℚ mirror of the delivered `s_R`. -/
def sRQ : Fin 4 → ℚ := fun m => rRQ m ^ 2

/-- The seat's tone family: the ternary sum family of the delivered
factor spectra, over `Fin 14 × Fin 8 × Fin 4` (448 tones). -/
def toneQ : Fin 14 × Fin 8 × Fin 4 → ℚ := sumFam3 s7Q s4Q sRQ

/-- The seat spectrum as a multiset over ℚ: `sumSpec3` of the
delivered factor spectra. -/
def seatSpecQ : Multiset ℚ := sumSpec3 s7Q s4Q sRQ

/-- The seat value set (the distinct `D²` tones at the seat). -/
def seatSet : Finset ℚ := seatSpecQ.toFinset

/-- The ternary excess: tones beyond distinctness (the ternary
analogue of RES-0's `excess`). -/
def excess3 (a : Fin 14 → ℚ) (b : Fin 8 → ℚ) (c : Fin 4 → ℚ) : ℕ :=
  14 * 8 * 4 - (sumSpec3 a b c).dedup.card

/-- `s7Q` on a realified index pair is the site square. -/
theorem s7Q_pair (k : Fin 7) (b : Fin 2) :
    s7Q ((finProdFinEquiv (m := 7) (n := 2)) (k, b)) = a7Q k ^ 2 := by
  simp [s7Q]

/-- `s4Q` on a realified index pair is the site square. -/
theorem s4Q_pair (k : Fin 4) (b : Fin 2) :
    s4Q ((finProdFinEquiv (m := 4) (n := 2)) (k, b)) = d4Q k ^ 2 := by
  simp [s4Q]

/-- Every `s7Q` value is nonnegative (it is a square). -/
theorem s7Q_nonneg (i : Fin 14) : 0 ≤ s7Q i := sq_nonneg _

/-- Every `s4Q` value is at least `1 / 64` (the centered ladder's
site squares are `1 / 64` and `9 / 64`). -/
theorem s4Q_ge (j : Fin 8) : 1 / 64 ≤ s4Q j := by
  have hgen : ∀ k : Fin 4, (1 : ℚ) / 64 ≤ d4Q k ^ 2 := by
    intro k
    fin_cases k <;> norm_num [d4Q]
  exact hgen _

/-- Every `sRQ` value is nonnegative (it is a square). -/
theorem sRQ_nonneg (m : Fin 4) : 0 ≤ sRQ m := sq_nonneg _

/-- Every seat tone is at least `1 / 64` — in particular no seat
tone is `0`, so the zero fence of `resCount` is vacuous at this
seat (the ground sector contributes no zero tone; cf. Q7CR-2's
`eigComp_ge`). -/
theorem toneQ_ge (p : Fin 14 × Fin 8 × Fin 4) : 1 / 64 ≤ toneQ p := by
  show 1 / 64 ≤ s7Q p.1 + s4Q p.2.1 + sRQ p.2.2
  have h1 := s7Q_nonneg p.1
  have h2 := s4Q_ge p.2.1
  have h3 := sRQ_nonneg p.2.2
  linarith

/-- No seat tone is zero. -/
theorem toneQ_ne_zero (p : Fin 14 × Fin 8 × Fin 4) : toneQ p ≠ 0 := by
  have h := toneQ_ge p
  positivity

/-! ## §2. RES-4a — the `D²` multiset-spectrum bridge

The delivered real spectra are the casts of the ℚ families, and
the cast of the ℚ ternary sum spectrum is the delivered composite
spectrum `spectrumQ7CR2`. This is exactly the bridge §4 priced as
RES-4a, and nothing more. -/

/-- RES-4a, factor cast: the delivered `a₇` is the cast of `a7Q`. -/
theorem a7Q_cast (k : Fin 7) : ((a7Q k : ℚ) : ℝ) = a₇ k := by
  fin_cases k <;> norm_num [a7Q, a₇]

/-- RES-4a, factor cast: the delivered `d₄` is the cast of `d4Q`. -/
theorem d4Q_cast (k : Fin 4) : ((d4Q k : ℚ) : ℝ) = d₄ k := by
  fin_cases k <;> norm_num [d4Q, d₄, z4Energy]

/-- RES-4a, factor cast: the delivered `r_R` is the cast of `rRQ`. -/
theorem rRQ_cast (k : Fin 4) : ((rRQ k : ℚ) : ℝ) = r_R k := by
  fin_cases k <;> norm_num [rRQ, r_R]

/-- RES-4a, spectrum cast: the delivered `s₇` is the cast of `s7Q`. -/
theorem s7Q_cast (i : Fin 14) : ((s7Q i : ℚ) : ℝ) = s₇ i := by
  show ((a7Q ((finProdFinEquiv (m := 7) (n := 2)).symm i).1 ^ 2 : ℚ) : ℝ)
      = a₇ ((finProdFinEquiv (m := 7) (n := 2)).symm i).1 ^ 2
  rw [Rat.cast_pow, a7Q_cast]

/-- RES-4a, spectrum cast: the delivered `s₄` is the cast of `s4Q`. -/
theorem s4Q_cast (j : Fin 8) : ((s4Q j : ℚ) : ℝ) = s₄ j := by
  show ((d4Q ((finProdFinEquiv (m := 4) (n := 2)).symm j).1 ^ 2 : ℚ) : ℝ)
      = d₄ ((finProdFinEquiv (m := 4) (n := 2)).symm j).1 ^ 2
  rw [Rat.cast_pow, d4Q_cast]

/-- RES-4a, spectrum cast: the delivered `s_R` is the cast of `sRQ`. -/
theorem sRQ_cast (m : Fin 4) : ((sRQ m : ℚ) : ℝ) = s_R m := by
  show ((rRQ m ^ 2 : ℚ) : ℝ) = r_R m ^ 2
  rw [Rat.cast_pow, rRQ_cast]

/-- The index equivalence between the ternary sum index
`Fin 14 × Fin 8 × Fin 4` and Q7CR-2's `compIndex`, through the
realification equivalences. -/
def seatEquiv : (Fin 14 × Fin 8 × Fin 4) ≃ compIndex where
  toFun := fun p => (((finProdFinEquiv (m := 7) (n := 2)).symm p.1,
    (finProdFinEquiv (m := 4) (n := 2)).symm p.2.1), p.2.2)
  invFun := fun q => ((finProdFinEquiv (m := 7) (n := 2)) q.1.1,
    (finProdFinEquiv (m := 4) (n := 2)) q.1.2, q.2)
  left_inv := fun ⟨i, j, m⟩ => by
    simp
  right_inv := fun ⟨⟨a, b⟩, m⟩ => by
    simp

/-- `seatEquiv` applied, in components. -/
theorem seatEquiv_apply (p : Fin 14 × Fin 8 × Fin 4) :
    seatEquiv p = (((finProdFinEquiv (m := 7) (n := 2)).symm p.1,
      (finProdFinEquiv (m := 4) (n := 2)).symm p.2.1), p.2.2) :=
  rfl

/-- Pointwise bridge: at corresponding indices, the delivered
composite eigenvalue is the cast of the ℚ tone. -/
theorem eigComp_seatEquiv (p : Fin 14 × Fin 8 × Fin 4) :
    eigComp (seatEquiv p) = ((toneQ p : ℚ) : ℝ) := by
  rw [seatEquiv_apply]
  show s₇c ((finProdFinEquiv (m := 7) (n := 2)).symm p.1)
      + s₄c ((finProdFinEquiv (m := 4) (n := 2)).symm p.2.1) + s_R p.2.2
      = ((s7Q p.1 + s4Q p.2.1 + sRQ p.2.2 : ℚ) : ℝ)
  have h7 : s₇c ((finProdFinEquiv (m := 7) (n := 2)).symm p.1) = s₇ p.1 := by
    show s₇ ((finProdFinEquiv (m := 7) (n := 2))
      ((finProdFinEquiv (m := 7) (n := 2)).symm p.1)) = s₇ p.1
    rw [Equiv.apply_symm_apply]
  have h4 : s₄c ((finProdFinEquiv (m := 4) (n := 2)).symm p.2.1) = s₄ p.2.1 := by
    show s₄ ((finProdFinEquiv (m := 4) (n := 2))
      ((finProdFinEquiv (m := 4) (n := 2)).symm p.2.1)) = s₄ p.2.1
    rw [Equiv.apply_symm_apply]
  rw [h7, h4, Rat.cast_add, Rat.cast_add, s7Q_cast, s4Q_cast, sRQ_cast]

/-- **RES-4a — the `D²` multiset-spectrum bridge.** The cast of the
ℚ ternary sum spectrum of the delivered factor spectra is exactly
Q7CR-2's certified composite spectrum `spectrumQ7CR2`. With
`dirac_sq_basisComp_eig`, this identifies `sumSpec3 s7Q s4Q sRQ`
(as a cast multiset) as the eigenvalue multiset of the
instantiated composite `D²`. -/
theorem seatSpecQ_cast_eq :
    seatSpecQ.map (fun q : ℚ => ((q : ℝ))) = spectrumQ7CR2 := by
  have h1 : seatSpecQ.map (fun q : ℚ => ((q : ℝ)))
      = Finset.univ.val.map (fun p => ((toneQ p : ℚ) : ℝ)) := by
    rw [seatSpecQ, sumSpec3, Multiset.map_map]
    rfl
  have h2 : Finset.univ.val.map (fun p => ((toneQ p : ℚ) : ℝ))
      = Finset.univ.val.map eigComp := by
    have hfun : (fun p => ((toneQ p : ℚ) : ℝ)) = eigComp ∘ seatEquiv := by
      funext p
      rw [Function.comp_apply, eigComp_seatEquiv]
    rw [hfun, ← Multiset.map_map]
    have hmap : Finset.univ.val.map seatEquiv = Finset.univ.val := by
      have h : (Finset.univ : Finset (Fin 14 × Fin 8 × Fin 4)).map
          seatEquiv.toEmbedding = Finset.univ :=
        Finset.map_univ_equiv seatEquiv
      have hval := congrArg Finset.val h
      rwa [Finset.map_val] at hval
    rw [hmap]
  rw [h1, h2]
  rfl

/-- The seat spectrum has exactly `448` tones with multiplicity
(RES-0's `card_sumSpec3` at the seat; cf. `spectrumQ7CR2_card`). -/
theorem seatSpecQ_card : seatSpecQ.card = 448 := by
  rw [seatSpecQ, card_sumSpec3]

/-! ## §3. Factor multiplicities, images, difference counts and ranges

All values below are the BRIDGE-1 seat computation's factor data
(`routeb-general-scratch/res4-seat.py`, run record `res4-run.txt`):
`s7Q` has values `9, 4, 1, 0` with multiplicities `4, 4, 4, 2`;
`s4Q` has values `9/64, 1/64` with multiplicities `4, 4`;
`sRQ` has values `0, 4` with multiplicities `2, 2`. -/

/-- Multiplicity transport for `s7Q`: a tone's multiplicity is
twice the number of Q⁷ sites carrying it (realification). -/
theorem multA_s7Q (v : ℚ) :
    multA s7Q v
      = 2 * (Finset.univ.filter (fun k : Fin 7 => a7Q k ^ 2 = v)).card := by
  have hset : Finset.univ.filter (fun i : Fin 14 => s7Q i = v)
      = (Finset.univ.filter (fun k : Fin 7 => a7Q k ^ 2 = v) ×ˢ
          (Finset.univ : Finset (Fin 2))).image
          (finProdFinEquiv (m := 7) (n := 2)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product]
    constructor
    · intro hi
      refine ⟨(finProdFinEquiv (m := 7) (n := 2)).symm i, ⟨?_, trivial⟩,
        Equiv.apply_symm_apply _ _⟩
      exact hi
    · rintro ⟨⟨k, b⟩, ⟨hk, -⟩, rfl⟩
      rw [s7Q_pair]
      exact hk
  show (Finset.univ.filter (fun i : Fin 14 => s7Q i = v)).card = _
  rw [hset, Finset.card_image_of_injective _
    (finProdFinEquiv (m := 7) (n := 2)).injective, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- Multiplicity transport for `s4Q` (realification, as for `s7Q`). -/
theorem multA_s4Q (v : ℚ) :
    multA s4Q v
      = 2 * (Finset.univ.filter (fun k : Fin 4 => d4Q k ^ 2 = v)).card := by
  have hset : Finset.univ.filter (fun j : Fin 8 => s4Q j = v)
      = (Finset.univ.filter (fun k : Fin 4 => d4Q k ^ 2 = v) ×ˢ
          (Finset.univ : Finset (Fin 2))).image
          (finProdFinEquiv (m := 4) (n := 2)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product]
    constructor
    · intro hj
      refine ⟨(finProdFinEquiv (m := 4) (n := 2)).symm j, ⟨?_, trivial⟩,
        Equiv.apply_symm_apply _ _⟩
      exact hj
    · rintro ⟨⟨k, b⟩, ⟨hk, -⟩, rfl⟩
      rw [s4Q_pair]
      exact hk
  show (Finset.univ.filter (fun j : Fin 8 => s4Q j = v)).card = _
  rw [hset, Finset.card_image_of_injective _
    (finProdFinEquiv (m := 4) (n := 2)).injective, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- The `s7Q` multiplicities at the seat (BRIDGE-1): the four
attained values and the three differences the (a3) evaluation
meets off the support. -/
theorem multA_s7Q_values :
    multA s7Q 9 = 4 ∧ multA s7Q 4 = 4 ∧ multA s7Q 1 = 4 ∧ multA s7Q 0 = 2
      ∧ multA s7Q 5 = 0 ∧ multA s7Q (-3) = 0 ∧ multA s7Q (-4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [multA_s7Q, Finset.card_filter,
    Fin.sum_univ_seven] <;> norm_num [a7Q]

/-- The `s4Q` multiplicities at the seat (BRIDGE-1). -/
theorem multA_s4Q_values :
    multA s4Q (1 / 64) = 4 ∧ multA s4Q (9 / 64) = 4 := by
  refine ⟨?_, ?_⟩ <;> rw [multA_s4Q, Finset.card_filter,
    Fin.sum_univ_four] <;> norm_num [d4Q]

/-- The `sRQ` multiplicities at the seat (BRIDGE-1). -/
theorem multA_sRQ_values :
    multA sRQ 0 = 2 ∧ multA sRQ 4 = 2 ∧ multA sRQ (-4) = 0 := by
  have h : ∀ v : ℚ, multA sRQ v
      = (Finset.univ.filter (fun m : Fin 4 => rRQ m ^ 2 = v)).card := fun v => rfl
  refine ⟨?_, ?_, ?_⟩ <;> rw [h, Finset.card_filter, Fin.sum_univ_four] <;>
    norm_num [rRQ]

/-- The image of `s7Q`: exactly `{9, 4, 1, 0}`. -/
theorem image_s7Q : Finset.univ.image s7Q = {9, 4, 1, 0} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    have hk : ∀ k : Fin 7, a7Q k ^ 2 = 9 ∨ a7Q k ^ 2 = 4 ∨ a7Q k ^ 2 = 1
        ∨ a7Q k ^ 2 = 0 := by
      intro k
      fin_cases k <;> norm_num [a7Q]
    have h := hk ((finProdFinEquiv (m := 7) (n := 2)).symm i).1
    rw [← hi]
    exact h
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (0, 0), by
        rw [s7Q_pair]; norm_num [a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (2, 0), by
        rw [s7Q_pair]; norm_num [a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (4, 0), by
        rw [s7Q_pair]; norm_num [a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (6, 0), by
        rw [s7Q_pair]; norm_num [a7Q]⟩

/-- The image of `s4Q`: exactly `{1 / 64, 9 / 64}`. -/
theorem image_s4Q : Finset.univ.image s4Q = {1 / 64, 9 / 64} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj⟩
    have hk : ∀ k : Fin 4, d4Q k ^ 2 = 1 / 64 ∨ d4Q k ^ 2 = 9 / 64 := by
      intro k
      fin_cases k <;> norm_num [d4Q]
    have h := hk ((finProdFinEquiv (m := 4) (n := 2)).symm j).1
    rw [← hj]
    exact h
  · rintro (rfl | rfl)
    · exact ⟨(finProdFinEquiv (m := 4) (n := 2)) (1, 0), by
        rw [s4Q_pair]; norm_num [d4Q]⟩
    · exact ⟨(finProdFinEquiv (m := 4) (n := 2)) (0, 0), by
        rw [s4Q_pair]; norm_num [d4Q]⟩

/-- The image of `sRQ`: exactly `{0, 4}`. -/
theorem image_sRQ : Finset.univ.image sRQ = {0, 4} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨m, rfl⟩
    fin_cases m <;> norm_num [sRQ, rRQ]
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num [sRQ, rRQ]⟩
    · exact ⟨1, by norm_num [sRQ, rRQ]⟩

/-- The difference-count function as a multiplicity inner product
over the family's image — the general form of RES-0's
`diffCount_zero` (which is the case `d = 0`): fibering the
difference pairs over the first tone's value. -/
theorem diffCount_eq_sum_mult {m : ℕ} (a : Fin m → ℚ) (d : ℚ) :
    diffCount a d
      = ∑ x ∈ Finset.univ.image a, multA a x * multA a (x - d) := by
  have hfiber : ∀ x : ℚ,
      (Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = d)).filter
          (fun p => a p.1 = x)
        = (Finset.univ.filter (fun i => a i = x)) ×ˢ
          (Finset.univ.filter (fun j => a j = x - d)) := by
    intro x
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      have h3 : a j = a i - d := by linarith
      rw [h3, h2]
    · rintro ⟨h2, h3⟩
      refine ⟨?_, h2⟩
      rw [h2, h3]
      ring
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = d))
    (t := Finset.univ.image a)
    (f := fun p : Fin m × Fin m => a p.1) (by
      intro p _
      exact Finset.mem_image_of_mem a (Finset.mem_univ p.1))
  rw [diffCount, h]
  apply Finset.sum_congr rfl
  intro x _
  rw [hfiber, Finset.card_product]
  rfl

/-- `diffCount s7Q 0 = 52` (BRIDGE-1: `4² + 4² + 4² + 2²`). -/
theorem diffCount_s7Q_zero : diffCount s7Q 0 = 52 := by
  obtain ⟨h9, h4, h1, h0, -, -, -⟩ := multA_s7Q_values
  rw [diffCount_eq_sum_mult, image_s7Q]
  norm_num [Finset.sum_insert, Finset.sum_singleton, sub_zero, h9, h4, h1, h0]

/-- `diffCount s7Q (±4) = 8` (BRIDGE-1: the only nonzero `s7Q`
difference that meets another factor's difference range, via the
`sRQ` gap `∓4`: pairs `(4, 0)` of tones, `4 · 2`). -/
theorem diffCount_s7Q_four :
    diffCount s7Q 4 = 8 ∧ diffCount s7Q (-4) = 8 := by
  obtain ⟨h9, h4, h1, h0, h5, h_3, h_4⟩ := multA_s7Q_values
  have h : diffCount s7Q 4 = 8 := by
    rw [diffCount_eq_sum_mult, image_s7Q]
    norm_num [Finset.sum_insert, Finset.sum_singleton, h9, h4, h1, h0, h5, h_3,
      h_4]
  refine ⟨h, ?_⟩
  have hneg : diffCount s7Q (-(4 : ℚ)) = diffCount s7Q 4 := diffCount_neg s7Q 4
  rw [show (-(4 : ℚ)) = (-4 : ℚ) by norm_num] at hneg
  rw [hneg]
  exact h


/-- `diffCount s4Q 0 = 32` (BRIDGE-1: `4² + 4²`). -/
theorem diffCount_s4Q_zero : diffCount s4Q 0 = 32 := by
  obtain ⟨h1, h9⟩ := multA_s4Q_values
  rw [diffCount_eq_sum_mult, image_s4Q]
  norm_num [Finset.sum_insert, Finset.sum_singleton, sub_zero, h1, h9]

/-- `diffCount sRQ 0 = 8`, `diffCount sRQ (±4) = 4` (BRIDGE-1:
`2² + 2²`; pairs `(4, 0)` of tones, `2 · 2`). -/
theorem diffCount_sRQ_values :
    diffCount sRQ 0 = 8 ∧ diffCount sRQ 4 = 4 ∧ diffCount sRQ (-4) = 4 := by
  obtain ⟨h0, h4, h_4⟩ := multA_sRQ_values
  have hz : diffCount sRQ 0 = 8 := by
    rw [diffCount_eq_sum_mult, image_sRQ]
    norm_num [Finset.sum_insert, Finset.sum_singleton, sub_zero, h0, h4]
  have hfour : diffCount sRQ 4 = 4 := by
    rw [diffCount_eq_sum_mult, image_sRQ]
    norm_num [Finset.sum_insert, Finset.sum_singleton, h0, h4, h_4]
  have hneg : diffCount sRQ (-(4 : ℚ)) = diffCount sRQ 4 := diffCount_neg sRQ 4
  rw [show (-(4 : ℚ)) = (-4 : ℚ) by norm_num] at hneg
  exact ⟨hz, hfour, by rw [hneg]; exact hfour⟩

/-- The difference range of `s7Q`, explicit (BRIDGE-1: support
`{0, ±1, ±3, ±4, ±5, ±8, ±9}`, 13 differences). -/
theorem diffRange_s7Q :
    diffRange s7Q = {0, 1, -1, 3, -3, 4, -4, 5, -5, 8, -8, 9, -9} := by
  ext d
  rw [mem_diffRange_iff]
  constructor
  · rintro ⟨i, j, hij⟩
    have hk : ∀ k k' : Fin 7, a7Q k ^ 2 - a7Q k' ^ 2
        ∈ ({0, 1, -1, 3, -3, 4, -4, 5, -5, 8, -8, 9, -9} : Finset ℚ) := by
      intro k k'
      fin_cases k <;> fin_cases k' <;>
        norm_num [a7Q, Finset.mem_insert, Finset.mem_singleton]
    have h := hk ((finProdFinEquiv (m := 7) (n := 2)).symm i).1
      ((finProdFinEquiv (m := 7) (n := 2)).symm j).1
    rw [← hij]
    exact h
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (0, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (6, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (6, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (4, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (4, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (2, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (6, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (6, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (2, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (2, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (0, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (4, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (0, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (6, 0), by
        norm_num [s7Q_pair, a7Q]⟩
    · exact ⟨(finProdFinEquiv (m := 7) (n := 2)) (6, 0),
        (finProdFinEquiv (m := 7) (n := 2)) (0, 0), by
        norm_num [s7Q_pair, a7Q]⟩

/-- The difference range of `s4Q`, explicit (BRIDGE-1:
`{0, ±1/8}` — the ladder's two site squares differ by `1/8`). -/
theorem diffRange_s4Q : diffRange s4Q = {0, 1 / 8, -1 / 8} := by
  ext d
  rw [mem_diffRange_iff]
  constructor
  · rintro ⟨j, j', hjj⟩
    have hk : ∀ k k' : Fin 4, d4Q k ^ 2 - d4Q k' ^ 2
        ∈ ({0, 1 / 8, -1 / 8} : Finset ℚ) := by
      intro k k'
      fin_cases k <;> fin_cases k' <;>
        norm_num [d4Q, Finset.mem_insert, Finset.mem_singleton]
    have h := hk ((finProdFinEquiv (m := 4) (n := 2)).symm j).1
      ((finProdFinEquiv (m := 4) (n := 2)).symm j').1
    rw [← hjj]
    exact h
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨(finProdFinEquiv (m := 4) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), by
        norm_num [s4Q_pair, d4Q]⟩
    · exact ⟨(finProdFinEquiv (m := 4) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), by
        norm_num [s4Q_pair, d4Q]⟩
    · exact ⟨(finProdFinEquiv (m := 4) (n := 2)) (1, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), by
        norm_num [s4Q_pair, d4Q]⟩

/-- The difference range of `sRQ`, explicit (BRIDGE-1: `{0, ±4}`). -/
theorem diffRange_sRQ : diffRange sRQ = {0, 4, -4} := by
  ext d
  rw [mem_diffRange_iff]
  constructor
  · rintro ⟨m, m', hmm⟩
    have hk : ∀ k k' : Fin 4, sRQ k - sRQ k'
        ∈ ({0, 4, -4} : Finset ℚ) := by
      intro k k'
      fin_cases k <;> fin_cases k' <;>
        norm_num [sRQ, rRQ, Finset.mem_insert, Finset.mem_singleton]
    rw [← hmm]
    exact hk m m'
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num [sRQ, rRQ]⟩
    · exact ⟨1, 0, by norm_num [sRQ, rRQ]⟩
    · exact ⟨0, 1, by norm_num [sRQ, rRQ]⟩


/-! ## §4. Deliverable 1 — `collCount3` at the seat, by (a3), with its pattern

BRIDGE-1 (run record `res4-run.txt`): the (a3) sum over difference
triples `d + e + f = 0` has exactly **three** nonzero terms:
`(0, 0, 0) ↦ 52 · 32 · 8 = 13312` (the within-factor degeneracy
term), and the two terms of the single pairwise face
`(4, 0, -4)` and `(-4, 0, 4)`, each `8 · 32 · 4 = 1024` — the
`s7Q`/`sRQ` shared gap `±4`, with `s4Q` on its diagonal (`e = 0`).
The genuinely ternary part (all three coordinates nonzero) is
**empty**: `s4Q`'s only nonzero differences are `±1/8`, which no
pair of integer differences from `s7Q`/`sRQ` can cancel. Total
`collCount3 = 13312 + 1024 + 1024 = 15360`. -/

/-- The (a3) support at the seat: the filtered difference-triple
finset is exactly `{(0,0,0), (4,0,-4), (-4,0,4)}`. -/
theorem a3_filter_eq :
    (diffRange s7Q ×ˢ diffRange s4Q ×ˢ diffRange sRQ).filter
        (fun t => t.1 + t.2.1 + t.2.2 = 0)
      = {(0, 0, 0), (4, 0, -4), (-4, 0, 4)} := by
  ext ⟨d, e, f⟩
  rw [diffRange_s7Q, diffRange_s4Q, diffRange_sRQ]
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hd, he, hf⟩, hsum⟩
    rcases he with rfl | rfl | rfl
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
        (try norm_num at hsum) <;> norm_num
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
        norm_num at hsum
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
        norm_num at hsum
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

/-- **(a3) at the seat, with its pattern.** `collCount3` of the
delivered spectra is the three-term decomposition: the
within-factor term `(0,0,0)`, plus the two terms of the single
pairwise face `(±4, 0, ∓4)` (the `s7Q`–`sRQ` shared gap, `s4Q`
diagonal). No genuinely ternary term occurs. This is RES-1's
`collCount3_eq_sum` evaluated at the seat. -/
theorem collCount3_seat_a3 :
    collCount3 s7Q s4Q sRQ
      = diffCount s7Q 0 * diffCount s4Q 0 * diffCount sRQ 0
        + diffCount s7Q 4 * diffCount s4Q 0 * diffCount sRQ (-4)
        + diffCount s7Q (-4) * diffCount s4Q 0 * diffCount sRQ 4 := by
  rw [collCount3_eq_sum, a3_filter_eq,
    Finset.sum_insert (by
      norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]),
    Finset.sum_insert (by
      norm_num [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]),
    Finset.sum_singleton]
  dsimp only
  rw [add_assoc]

/-- **`collCount3` at the seat: `15360`** (BRIDGE-1), by the (a3)
decomposition `13312 + 1024 + 1024`. -/
theorem collCount3_seat : collCount3 s7Q s4Q sRQ = 15360 := by
  obtain ⟨h7, h7'⟩ := diffCount_s7Q_four
  obtain ⟨hz, h4, h_4⟩ := diffCount_sRQ_values
  rw [collCount3_seat_a3, diffCount_s7Q_zero, diffCount_s4Q_zero, h7, h7', hz,
    h4, h_4]

/-- The ternary diagonal at the seat (RES-1's `collCount3_diag_le`):
`448 ≤ collCount3` — the diagonal contributes exactly `448` of the
`15360` collision pairs. -/
theorem collCount3_seat_diag : 448 ≤ collCount3 s7Q s4Q sRQ := by
  have h := collCount3_diag_le s7Q s4Q sRQ
  norm_num at h
  exact h


/-! ## §5. Deliverable 2 — the named-ratio counts over the 448 tones

The seat's tones all have the form `(2w + 1) / 64` with `w : ℤ`:
the `s7Q` and `sRQ` parts are integers, and the `s4Q` part is
`1/64` or `9/64` (an odd sixty-fourth). Hence every tone has
2-adic valuation exactly `-6`. Consequences, all proved below:
the unison count (zero-fenced) is the tone family's self-overlap
`∑ mult² = 15360` — the same number as `collCount3`, by the same
fiber count; the octave count `resCount 2 1` is `0` (an octave
pair would force an odd numerator to equal an even one); the
fifth count `resCount 3 2` is `0` (it would force an even
numerator to equal an odd one). The zero fence is vacuous here:
no seat tone is `0` (`toneQ_ge`), so the fenced and unfenced
counts agree at these ratios — the fence correction
`multA · 0 · multA · 0` is `0` because the tone `0` has
multiplicity `0` in the seat spectrum (BRIDGE-1). -/

/-- The `s7Q` tones are integers (site squares of integers). -/
theorem s7Q_int (i : Fin 14) : ∃ z : ℤ, s7Q i = (z : ℚ) := by
  have hk : ∀ k : Fin 7, ∃ z : ℤ, a7Q k ^ 2 = (z : ℚ) := by
    intro k
    fin_cases k
    · exact ⟨9, by norm_num [a7Q]⟩
    · exact ⟨9, by norm_num [a7Q]⟩
    · exact ⟨4, by norm_num [a7Q]⟩
    · exact ⟨4, by norm_num [a7Q]⟩
    · exact ⟨1, by norm_num [a7Q]⟩
    · exact ⟨1, by norm_num [a7Q]⟩
    · exact ⟨0, by norm_num [a7Q]⟩
  exact hk _

/-- The `sRQ` tones are integers (site squares of integers). -/
theorem sRQ_int (m : Fin 4) : ∃ z : ℤ, sRQ m = (z : ℚ) := by
  fin_cases m
  · exact ⟨0, by norm_num [sRQ, rRQ]⟩
  · exact ⟨4, by norm_num [sRQ, rRQ]⟩
  · exact ⟨4, by norm_num [sRQ, rRQ]⟩
  · exact ⟨0, by norm_num [sRQ, rRQ]⟩

/-- The `s4Q` tones are odd sixty-fourths: `1/64` or `9/64`. -/
theorem s4Q_odd (j : Fin 8) : ∃ w : ℤ, s4Q j = (2 * (w : ℚ) + 1) / 64 := by
  have hk : ∀ k : Fin 4, ∃ w : ℤ, d4Q k ^ 2 = (2 * (w : ℚ) + 1) / 64 := by
    intro k
    fin_cases k
    · exact ⟨4, by norm_num [d4Q]⟩
    · exact ⟨0, by norm_num [d4Q]⟩
    · exact ⟨0, by norm_num [d4Q]⟩
    · exact ⟨4, by norm_num [d4Q]⟩
  exact hk _

/-- **The seat tone form.** Every one of the 448 tones is an odd
sixty-fourth: `toneQ p = (2w + 1) / 64` for some `w : ℤ`. -/
theorem toneQ_odd_form (p : Fin 14 × Fin 8 × Fin 4) :
    ∃ w : ℤ, toneQ p = (2 * (w : ℚ) + 1) / 64 := by
  obtain ⟨z1, h1⟩ := s7Q_int p.1
  obtain ⟨w4, h4⟩ := s4Q_odd p.2.1
  obtain ⟨z3, h3⟩ := sRQ_int p.2.2
  refine ⟨32 * (z1 + z3) + w4, ?_⟩
  show s7Q p.1 + s4Q p.2.1 + sRQ p.2.2
      = (2 * ((32 * (z1 + z3) + w4 : ℤ) : ℚ) + 1) / 64
  rw [h1, h4, h3]
  push_cast
  ring

/-- The index equivalence `Fin 448 ≃ Fin 14 × Fin 8 × Fin 4`
through the product equivalences (`448 = 14 · (8 · 4)`), written
as an explicit structure so its `symm` computes componentwise. -/
def idxEquiv : Fin 448 ≃ Fin 14 × Fin 8 × Fin 4 where
  toFun := fun i =>
    let p := (finProdFinEquiv (m := 14) (n := 32)).symm i
    (p.1, (finProdFinEquiv (m := 8) (n := 4)).symm p.2)
  invFun := fun q => (finProdFinEquiv (m := 14) (n := 32))
    (q.1, (finProdFinEquiv (m := 8) (n := 4)) q.2)
  left_inv := fun i => by
    simp only [Equiv.apply_symm_apply]
    exact Equiv.apply_symm_apply _ _
  right_inv := fun ⟨a, b⟩ => by
    simp only [Equiv.symm_apply_apply]

/-- The 448 seat tones as a `Fin 448` family (the form `resCount`
consumes), transported along `idxEquiv`. -/
def tone448 : Fin 448 → ℚ := fun i => toneQ (idxEquiv i)

/-- Transport of `resCount` along `idxEquiv`: the fenced count
over the `Fin 448` family is the fenced count over the ternary
index, by the product bijection `idxEquiv × idxEquiv`. -/
theorem resCount_tone448 (p q : ℕ) :
    resCount p q tone448 tone448
      = (Finset.univ.filter (fun ij : (Fin 14 × Fin 8 × Fin 4)
          × (Fin 14 × Fin 8 × Fin 4) =>
          (q : ℚ) * toneQ ij.1 = (p : ℚ) * toneQ ij.2
            ∧ toneQ ij.1 ≠ 0)).card := by
  unfold resCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv
    (Equiv.prodCongr idxEquiv idxEquiv) (fun _ => Iff.rfl))

/-- **Unison at the seat (zero-fenced): `resCount 1 1 = 15360`.**
The fenced unison filter over tone pairs is exactly the
`collCount3` collision filter (the fence is vacuous: no tone is
`0`), so the unison count is the self-overlap `∑ mult²`, equal
to `collCount3` at the seat. -/
theorem resCount_unison_seat : resCount 1 1 tone448 tone448 = 15360 := by
  rw [resCount_tone448]
  have hfil : Finset.univ.filter (fun ij : (Fin 14 × Fin 8 × Fin 4)
        × (Fin 14 × Fin 8 × Fin 4) =>
        ((1 : ℕ) : ℚ) * toneQ ij.1 = ((1 : ℕ) : ℚ) * toneQ ij.2
          ∧ toneQ ij.1 ≠ 0)
      = Finset.univ.filter (fun ij : (Fin 14 × Fin 8 × Fin 4)
          × (Fin 14 × Fin 8 × Fin 4) =>
          sumFam3 s7Q s4Q sRQ ij.1 = sumFam3 s7Q s4Q sRQ ij.2) := by
    apply Finset.filter_congr
    intro ij _
    simp only [Nat.cast_one, one_mul]
    exact ⟨fun h => h.1, fun h => ⟨h, toneQ_ne_zero _⟩⟩
  rw [hfil]
  show collCount3 s7Q s4Q sRQ = 15360
  exact collCount3_seat

/-- **Octave at the seat (zero-fenced): `resCount 2 1 = 0`.**
An octave pair `tone = 2 · tone'` would force the odd numerator
`2w + 1` of one tone to equal the even number `2 · (2w' + 1)`
from the other — impossible. The seat is perfectly octave-deaf
at the level of exact tone ratios (its octave *classes* are
censused in §7). -/
theorem resCount_octave_seat : resCount 2 1 tone448 tone448 = 0 := by
  rw [resCount_tone448, Finset.filter_false_of_mem (fun ij _ h => ?_),
    Finset.card_empty]
  obtain ⟨w1, hw1⟩ := toneQ_odd_form ij.1
  obtain ⟨w2, hw2⟩ := toneQ_odd_form ij.2
  have h1 : toneQ ij.1 = 2 * toneQ ij.2 := by
    have hh := h.1
    simpa using hh
  rw [hw1, hw2] at h1
  have h3 : (2 * (w1 : ℚ) + 1) = 2 * (2 * (w2 : ℚ) + 1) := by
    linear_combination h1 * 64
  have h4 : ((2 * w1 + 1 : ℤ) : ℚ) = ((2 * (2 * w2 + 1) : ℤ) : ℚ) := by
    push_cast
    exact h3
  have h5 : (2 * w1 + 1 : ℤ) = 2 * (2 * w2 + 1) := by exact_mod_cast h4
  omega

/-- **Fifth at the seat (zero-fenced): `resCount 3 2 = 0`.**
A fifth pair `2 · tone = 3 · tone'` would force the even number
`2 · (2w + 1)` to equal the odd number `3 · (2w' + 1)` —
impossible. -/
theorem resCount_fifth_seat : resCount 3 2 tone448 tone448 = 0 := by
  rw [resCount_tone448, Finset.filter_false_of_mem (fun ij _ h => ?_),
    Finset.card_empty]
  obtain ⟨w1, hw1⟩ := toneQ_odd_form ij.1
  obtain ⟨w2, hw2⟩ := toneQ_odd_form ij.2
  have h1 : 2 * toneQ ij.1 = 3 * toneQ ij.2 := by
    have hh := h.1
    norm_num at hh
    exact hh
  rw [hw1, hw2] at h1
  have h3 : (2 : ℚ) * (2 * (w1 : ℚ) + 1) = 3 * (2 * (w2 : ℚ) + 1) := by
    linear_combination h1 * 64
  have h4 : ((2 * (2 * w1 + 1) : ℤ) : ℚ) = ((3 * (2 * w2 + 1) : ℤ) : ℚ) := by
    push_cast
    exact h3
  have h5 : (2 * (2 * w1 + 1) : ℤ) = 3 * (2 * w2 + 1) := by exact_mod_cast h4
  omega


/-! ## §6. The forcing check at the seat (K-RES-1 data)

BRIDGE-1 forcing data: denominators cleared (all tones are
sixty-fourths), the 448 sums land in a value set of size
`K_seat = 14`. The pigeonhole floor is `excess ≥ 448 − 14 = 434`;
the proved excess is `434`; the difference is `0`. The
multiplicity form of the floor (RES-2's `exists_sumMult_mul_ge`
shape) is witnessed explicitly: the value `257/64` carries
multiplicity `48`, and `14 · 48 = 672 ≥ 448`, with
`48 ≥ ⌈448 / 14⌉ = 32`. -/

/-- Count bridge, ternary form (RES-0's `count_sumSpec`, ternary):
the multiplicity of `v` in `sumSpec3` is the number of tone
triples summing to `v`. -/
theorem count_sumSpec3 {m n l : ℕ} (a : Fin m → ℚ) (b : Fin n → ℚ)
    (c : Fin l → ℚ) (v : ℚ) :
    (sumSpec3 a b c).count v
      = (Finset.univ.filter (fun p => sumFam3 a b c p = v)).card := by
  have hf : Finset.univ.filter (fun p => v = sumFam3 a b c p)
      = Finset.univ.filter (fun p => sumFam3 a b c p = v) :=
    Finset.filter_congr (fun p _ => eq_comm)
  rw [sumSpec3, Multiset.count_map, ← Finset.filter_val, hf]
  rfl

/-- The ternary multiplicity formula: the multiplicity of `v` in
the sum spectrum is the sum over the factors' images of the
product of multiplicities at triples summing to `v` — fibering
the tone triples over their factor values. -/
theorem count_sumSpec3_eq {m n l : ℕ} (a : Fin m → ℚ) (b : Fin n → ℚ)
    (c : Fin l → ℚ) (v : ℚ) :
    (sumSpec3 a b c).count v
      = ∑ x ∈ Finset.univ.image a, ∑ y ∈ Finset.univ.image b,
          ∑ z ∈ Finset.univ.image c,
            (if x + y + z = v then multA a x * multA b y * multA c z
              else 0) := by
  rw [count_sumSpec3]
  have hfiber : ∀ x y z : ℚ,
      (Finset.univ.filter (fun p : Fin m × Fin n × Fin l =>
          sumFam3 a b c p = v)).filter
          (fun p => (a p.1, b p.2.1, c p.2.2) = (x, y, z))
        = if x + y + z = v then
            (Finset.univ.filter (fun i => a i = x)) ×ˢ
              (Finset.univ.filter (fun j => b j = y)) ×ˢ
                (Finset.univ.filter (fun k => c k = z))
          else ∅ := by
    intro x y z
    by_cases ht : x + y + z = v
    · rw [if_pos ht]
      ext ⟨i, j, k⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨-, hi, hj, hk⟩
        exact ⟨hi, hj, hk⟩
      · rintro ⟨hi, hj, hk⟩
        refine ⟨?_, hi, hj, hk⟩
        show a i + b j + c k = v
        rw [hi, hj, hk]
        exact ht
    · rw [if_neg ht, Finset.filter_false_of_mem (fun p hp hpf => ?_)]
      have hv : sumFam3 a b c p = v := (Finset.mem_filter.mp hp).2
      have h1 : a p.1 = x := congrArg Prod.fst hpf
      have h2 : b p.2.1 = y := congrArg (fun t => t.2.1) hpf
      have h3 : c p.2.2 = z := congrArg (fun t => t.2.2) hpf
      exact ht (by rw [← h1, ← h2, ← h3]; exact hv)
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun p : Fin m × Fin n × Fin l =>
        sumFam3 a b c p = v))
    (t := Finset.univ.image a ×ˢ Finset.univ.image b ×ˢ Finset.univ.image c)
    (f := fun p : Fin m × Fin n × Fin l => (a p.1, b p.2.1, c p.2.2)) (by
      intro p _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem a (Finset.mem_univ p.1),
          Finset.mem_product.mpr
            ⟨Finset.mem_image_of_mem b (Finset.mem_univ p.2.1),
              Finset.mem_image_of_mem c (Finset.mem_univ p.2.2)⟩⟩)
  rw [h]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  rw [hfiber]
  by_cases htz : x + y + z = v
  · rw [if_pos htz, if_pos htz, Finset.card_product, Finset.card_product]
    simp only [multA, mul_assoc]
  · rw [if_neg htz, if_neg htz, Finset.card_empty]

/-- The `tone448` multiset is the seat spectrum: transporting
`Finset.univ` along `idxEquiv`. -/
theorem tone448_multiset : Finset.univ.val.map tone448 = seatSpecQ := by
  have e : Finset.univ.val.map tone448
      = Finset.univ.val.map (toneQ ∘ idxEquiv) := rfl
  have h2 : Finset.univ.val.map idxEquiv = Finset.univ.val := by
    have h : (Finset.univ : Finset (Fin 448)).map idxEquiv.toEmbedding
        = Finset.univ := Finset.map_univ_equiv idxEquiv
    have hval := congrArg Finset.val h
    rwa [Finset.map_val] at hval
  rw [e, ← Multiset.map_map, h2]
  rfl

/-- **The multiplicity of `257/64` at the seat: `48`** (BRIDGE-1:
the two carrying combos `(4, 1/64, 0)` and `(0, 1/64, 4)`,
`4·4·2 + 2·4·2 = 32 + 16`). This is the seat's largest
multiplicity, the forcing witness of §6. -/
theorem multA_tone448_257 : multA tone448 (257 / 64) = 48 := by
  obtain ⟨h9, h4, h1, h0, -, -, -⟩ := multA_s7Q_values
  obtain ⟨g1, g9⟩ := multA_s4Q_values
  obtain ⟨r0, r4, -⟩ := multA_sRQ_values
  rw [multA_eq_count, tone448_multiset]
  show (sumSpec3 s7Q s4Q sRQ).count (257 / 64) = 48
  rw [count_sumSpec3_eq, image_s7Q, image_s4Q, image_sRQ]
  norm_num [Finset.sum_insert, Finset.sum_singleton, h9, h4, h1, h0, g1, g9,
    r0, r4]


/-- The seat value set is the image of the tone family. -/
theorem seatSet_eq_image : seatSet = Finset.univ.image toneQ := by
  ext v
  simp only [seatSet, Multiset.mem_toFinset, seatSpecQ, sumSpec3,
    Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, hp⟩

/-- The 448 tones take exactly the 14 BRIDGE-1 values: the image
of `toneQ` is the explicit finset below (from the factor images
`{9,4,1,0} × {1/64, 9/64} × {0,4}`: 16 combos, two collisions —
`257/64 = 4 + 1/64 + 0 = 0 + 1/64 + 4` and
`265/64 = 4 + 9/64 + 0 = 0 + 9/64 + 4`). -/
theorem image_toneQ :
    Finset.univ.image toneQ
      = {1 / 64, 9 / 64, 65 / 64, 73 / 64, 257 / 64, 265 / 64, 321 / 64,
          329 / 64, 513 / 64, 521 / 64, 577 / 64, 585 / 64, 833 / 64,
          841 / 64} := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨p, hp⟩
    have hx : s7Q p.1 = 9 ∨ s7Q p.1 = 4 ∨ s7Q p.1 = 1 ∨ s7Q p.1 = 0 := by
      have hmem : s7Q p.1 ∈ ({9, 4, 1, 0} : Finset ℚ) :=
        image_s7Q ▸ Finset.mem_image_of_mem s7Q (Finset.mem_univ p.1)
      simpa using hmem
    have hy : s4Q p.2.1 = 1 / 64 ∨ s4Q p.2.1 = 9 / 64 := by
      have hmem : s4Q p.2.1 ∈ ({1 / 64, 9 / 64} : Finset ℚ) :=
        image_s4Q ▸ Finset.mem_image_of_mem s4Q (Finset.mem_univ p.2.1)
      simpa using hmem
    have hz : sRQ p.2.2 = 0 ∨ sRQ p.2.2 = 4 := by
      have hmem : sRQ p.2.2 ∈ ({0, 4} : Finset ℚ) :=
        image_sRQ ▸ Finset.mem_image_of_mem sRQ (Finset.mem_univ p.2.2)
      simpa using hmem
    have htv : toneQ p = s7Q p.1 + s4Q p.2.1 + sRQ p.2.2 := rfl
    rw [← hp, htv]
    rcases hx with e1 | e1 | e1 | e1 <;> rcases hy with e2 | e2 <;>
      rcases hz with e3 | e3 <;> rw [e1, e2, e3] <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl)
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (6, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (6, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 1), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (4, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 1), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 1), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (2, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 1), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 0), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (1, 0), 1), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩
    · exact ⟨((finProdFinEquiv (m := 7) (n := 2)) (0, 0),
        (finProdFinEquiv (m := 4) (n := 2)) (0, 0), 1), by
        norm_num [toneQ, sumFam3, s7Q_pair, s4Q_pair, sRQ, rRQ, a7Q, d4Q]⟩

/-- The seat value set is the explicit 14-element finset. -/
theorem seatSet_eq :
    seatSet = {1 / 64, 9 / 64, 65 / 64, 73 / 64, 257 / 64, 265 / 64,
      321 / 64, 329 / 64, 513 / 64, 521 / 64, 577 / 64, 585 / 64, 833 / 64,
      841 / 64} :=
  seatSet_eq_image.trans image_toneQ

/-- **`K_seat = 14`**: the 448 seat tones take exactly 14 distinct
values. -/
theorem seatSet_card : seatSet.card = 14 := by
  rw [seatSet_eq]
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert,
    Finset.mem_singleton]

/-- The dedup card of the seat spectrum is `K_seat`. -/
theorem seat_dedup_card :
    (sumSpec3 s7Q s4Q sRQ).dedup.card = 14 := by
  have h1 : (sumSpec3 s7Q s4Q sRQ).dedup.card
      = (sumSpec3 s7Q s4Q sRQ).toFinset.card := by
    rw [← Multiset.toFinset_card_of_nodup (Multiset.nodup_dedup _),
      Multiset.toFinset_dedup]
  rw [h1]
  show seatSet.card = 14
  exact seatSet_card

/-- **The proved excess at the seat: `excess3 = 434`** —
`448 − K_seat`, exactly the pigeonhole floor. -/
theorem excess3_seat : excess3 s7Q s4Q sRQ = 434 := by
  show 14 * 8 * 4 - (sumSpec3 s7Q s4Q sRQ).dedup.card = 434
  rw [seat_dedup_card]

/-- **The forcing check at the seat (the §3 floor, ternary form).**
The floor `448 − K_seat ≤ excess3` holds, the proved excess is
`434`, and the difference between the proved excess and the
floor is `0`: every coincidence at this seat, at the level of
the distinct-value count, is pigeonhole rent. The seat's further
content is the (a3) pattern of §4, not the count. -/
theorem forcing_seat :
    448 - seatSet.card ≤ excess3 s7Q s4Q sRQ
      ∧ excess3 s7Q s4Q sRQ = 434
      ∧ excess3 s7Q s4Q sRQ - (448 - seatSet.card) = 0 := by
  refine ⟨?_, excess3_seat, ?_⟩ <;> norm_num [seatSet_card, excess3_seat]

/-- **The multiplicity floor at the seat, witnessed** (RES-2's
multiplicity form): `K_seat · mult(257/64) = 14 · 48 = 672 ≥ 448`,
and `mult(257/64) = 48 ≥ ⌈448 / 14⌉ = 32`. -/
theorem mult_floor_seat :
    448 ≤ seatSet.card * multA tone448 (257 / 64)
      ∧ 32 ≤ multA tone448 (257 / 64) := by
  refine ⟨?_, ?_⟩ <;> norm_num [seatSet_card, multA_tone448_257]

/-! ## §7. Deliverable 3 — the octave census of the 448 tones

BRIDGE-1 census: every seat value is an odd sixty-fourth, so its
odd part is its (odd) numerator over `64` — all 14 values lie in
**distinct** octave classes (14 classes met, one value per class),
and no doubling of a seat value is a seat value: the longest
`OctChain` in the seat value set has length `0`. Read against
(c3)'s poles: this is the dispersion end — maximally far from
the geometric ladder's single-class concentration. Per (c2), no
closure statement is statable and none is stated. -/

/-- Every seat value is positive (it is a tone, and tones are
`≥ 1/64`). -/
theorem seatSet_pos : ∀ v ∈ seatSet, 0 < v := by
  intro v hv
  rw [seatSet_eq_image] at hv
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hv
  rw [← hp]
  have h := toneQ_ge p
  linarith

/-- Every seat value has the odd-sixty-fourth form. -/
theorem seatSet_odd_form :
    ∀ v ∈ seatSet, ∃ w : ℤ, v = (2 * (w : ℚ) + 1) / 64 := by
  intro v hv
  rw [seatSet_eq_image] at hv
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hv
  obtain ⟨w, hw⟩ := toneQ_odd_form p
  exact ⟨w, by rw [← hp]; exact hw⟩

/-- **Class separation at the seat.** No two distinct seat values
are octave-equivalent: if `x, y` are seat values with
`OctEq x y`, then `x = y`. (Both are odd sixty-fourths;
`y = 2^k · x` with `k ≠ 0` would force an odd numerator to equal
an even one, in either direction.) Hence the 14 seat values meet
14 distinct octave classes, one value per class. -/
theorem not_octEq_of_seatSet :
    ∀ x ∈ seatSet, ∀ y ∈ seatSet, OctEq x y → x = y := by
  intro x hx y hy hOct
  obtain ⟨a, hax⟩ := seatSet_odd_form x hx
  obtain ⟨b, hby⟩ := seatSet_odd_form y hy
  obtain ⟨k, hk⟩ := hOct
  by_cases hk0 : 0 ≤ k
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = k :=
      ⟨k.natAbs, Int.ofNat_natAbs_of_nonneg hk0⟩
    rw [zpow_natCast] at hk
    have hi : (2 * b + 1 : ℤ) = (2 : ℤ) ^ n * (2 * a + 1) := by
      have h' : ((2 * b + 1 : ℤ) : ℚ)
          = (((2 : ℤ) ^ n * (2 * a + 1) : ℤ) : ℚ) := by
        push_cast
        rw [hby, hax] at hk
        linear_combination hk * 64
      exact_mod_cast h'
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [pow_zero, one_mul] at hi
      have hab : a = b := by omega
      rw [hax, hby, hab]
    · exfalso
      have hdvd : (2 : ℤ) ∣ (2 * b + 1) := by
        rw [hi]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)) _
      omega
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := by
      refine ⟨k.natAbs, ?_⟩
      have h2 : ((k.natAbs : ℤ)) = -k :=
        Int.ofNat_natAbs_of_nonpos (le_of_lt (not_le.mp hk0))
      omega
    have hn : n ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, neg_zero] at hk0
      exact hk0 (le_refl 0)
    exfalso
    have hk2 : x = (2 : ℚ) ^ n * y := by
      have hne : ((2 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [zpow_neg, zpow_natCast] at hk
      have hmul : (2 : ℚ) ^ n * y = x := by
        rw [hk, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      exact hmul.symm
    have hi : (2 * a + 1 : ℤ) = (2 : ℤ) ^ n * (2 * b + 1) := by
      have h' : ((2 * a + 1 : ℤ) : ℚ)
          = (((2 : ℤ) ^ n * (2 * b + 1) : ℤ) : ℚ) := by
        push_cast
        rw [hax, hby] at hk2
        linear_combination hk2 * 64
      exact_mod_cast h'
    have hdvd : (2 : ℤ) ∣ (2 * a + 1) := by
      rw [hi]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 hn) _
    omega

/-- Octave chains of length `0` exist at every seat value
(the value itself). -/
theorem octChain_zero_seat :
    ∀ x ∈ seatSet, OctChain seatSet x 0 := by
  intro x hx i hi
  interval_cases i
  simpa using hx

/-- No octave chain of length `1` exists at any seat value:
doubling a seat value leaves the seat value set (by RES-0's
`octEq_two_mul` and the class separation above). Hence the
longest `OctChain` in the seat value set has length exactly
`0`. -/
theorem no_octChain_one_seat :
    ∀ x ∈ seatSet, ¬ OctChain seatSet x 1 := by
  intro x hx hch
  have h2 : (2 : ℚ) ^ 1 * x ∈ seatSet := hch 1 le_rfl
  rw [pow_one] at h2
  have heq : x = (2 : ℚ) * x :=
    not_octEq_of_seatSet x hx ((2 : ℚ) * x) h2 (octEq_two_mul x)
  have hpos := seatSet_pos x hx
  linarith

/-- **The octave census at the seat** (deliverable 3, assembled):
`K_seat = 14` values; no two distinct values share an octave
class (14 classes met, one value per class — the dispersion
pole of (c3), opposite the ladder's one class); chains of
length `0` at every value and no chain of length `1`: the
longest `OctChain` has length `0`. No closure statement is
made (c2). -/
theorem seat_octave_census :
    seatSet.card = 14
      ∧ (∀ x ∈ seatSet, ∀ y ∈ seatSet, OctEq x y → x = y)
      ∧ (∀ x ∈ seatSet, OctChain seatSet x 0)
      ∧ (∀ x ∈ seatSet, ¬ OctChain seatSet x 1) :=
  ⟨seatSet_card, not_octEq_of_seatSet, octChain_zero_seat,
    no_octChain_one_seat⟩

end ThetLogos

#print axioms ThetLogos.seatSpecQ_cast_eq
#print axioms ThetLogos.collCount3_seat_a3
#print axioms ThetLogos.collCount3_seat
#print axioms ThetLogos.resCount_unison_seat
#print axioms ThetLogos.resCount_octave_seat
#print axioms ThetLogos.resCount_fifth_seat
#print axioms ThetLogos.forcing_seat
#print axioms ThetLogos.multA_tone448_257
#print axioms ThetLogos.seat_octave_census
