import Mathlib.Tactic
import ThetLogos.DialOneSwapOrbit

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit

/-!
# CLS-2G — the toggle-orbit group-law seam

NO CLAIM; Dial 1 = 0. CLS-2 (`DialOneSwapOrbit`) landed the
16-point orbit as a classified SET (membership + weights,
completed by CLS-2b), with the group-law seam named open:
"the orbit is classified as a set with membership and
weights; the composition law is bookkeeping the lane has
not needed." This module closes that seam.

The frozen composition form, in the landed vocabulary
(bits are the landed `Fin 4 → Bool` patterns; bit addition
is pointwise `xor`, the (ℤ/2)⁴ addition in that vocabulary):

* The per-bit modification as landed in `orbitRep` is, at
  each toggle seat, the passage `a.u1 ↔ star a.u1`:
  `pi1`'s entries at the seats `s8, s9` (bit 0) and
  `uSeat c, dSeat c` (bit `swapIdx c`) are exactly
  `a.u1` / `star a.u1`, and `orbitRep`'s corrections
  (`orbitCorrD`, `orbitCorrS c`) move each such entry to
  the other one. The toggle map `toggleMap b` is that
  modification read as a map on representations:
  entrywise conjugation (`star`) at the diagonal seats
  whose bit is set in `b`, identity elsewhere. The four
  seat pairs `{8,9}, {10,11}, {12,13}, {14,15}` are
  pairwise disjoint — this is what makes composition
  hold, and it is proved, not assumed.
* Composition form: `toggleMap (bitsAdd b₁ b₂)
  = toggleMap b₁ ∘ toggleMap b₂`, with
  `orbitRep b = toggleMap b pi1` — the orbit is the image
  of a group action of (ℤ/2)⁴.

**Verdict: the composition law is PROVED.** K-CLS-2G does
NOT fire. Corollaries landed: `T_0 = id`
(`toggleMap_zero`), involutivity
(`toggleMap_involutive`), distinct-bit commutativity
(`toggleMap_bitPat_commute`). CLS-2/2b untouched; no
membership, weight, or exclusion statement changes.
-/

namespace ThetLogos.DialOneSwapOrbitGroupLaw

/-! ## §0. The frozen vocabulary -/

/-- Bit addition on the landed bit patterns
`Fin 4 → Bool`: pointwise `xor` — the (ℤ/2)⁴ addition in
the landed vocabulary. -/
def bitsAdd (b₁ b₂ : Fin 4 → Bool) : Fin 4 → Bool :=
  fun i => xor (b₁ i) (b₂ i)

/-- Whether the diagonal seat `i` is toggled by the bit
pattern `b`: bit 0 owns seats 8, 9 (`s8`, `s9`); bit 1
owns seats 10, 11 (`uSeat 0`, `dSeat 0`); bit 2 owns
seats 12, 13 (`uSeat 1`, `dSeat 1`); bit 3 owns seats
14, 15 (`uSeat 2`, `dSeat 2`). The four pairs are
disjoint. -/
def toggled (b : Fin 4 → Bool) (i : Fin 32) : Bool :=
  (b 0 && ((i.val == 8) || (i.val == 9))) ||
  (b 1 && ((i.val == 10) || (i.val == 11))) ||
  (b 2 && ((i.val == 12) || (i.val == 13))) ||
  (b 3 && ((i.val == 14) || (i.val == 15)))

/-- The toggle map `T_b` on representations, defined from
`orbitRep`'s own per-bit modifications as landed: at a
diagonal seat whose bit is set, the landed corrections
send `pi1`'s entry `a.u1` to `star a.u1` and
`star a.u1` to `a.u1` — entrywise conjugation. `T_b`
applies exactly that conjugation at the seats `b`
selects, and is the identity at every other entry. -/
def toggleMap (b : Fin 4 → Bool)
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    AF → Matrix (Fin 32) (Fin 32) ℂ :=
  fun a i j =>
    if toggled b i = true ∧ i = j then star (π a i j)
    else π a i j

/-- The singleton bit pattern with only bit `k` set. -/
def bitPat (k : Fin 4) : Fin 4 → Bool := fun j => decide (j = k)

/-! ## §1. The composition law -/

theorem bitsAdd_apply (b₁ b₂ : Fin 4 → Bool) (i : Fin 4) :
    bitsAdd b₁ b₂ i = xor (b₁ i) (b₂ i) :=
  rfl

theorem bitsAdd_comm (b₁ b₂ : Fin 4 → Bool) :
    bitsAdd b₁ b₂ = bitsAdd b₂ b₁ := by
  funext i
  show xor (b₁ i) (b₂ i) = xor (b₂ i) (b₁ i)
  cases b₁ i <;> cases b₂ i <;> rfl

theorem bitsAdd_self (b : Fin 4 → Bool) :
    bitsAdd b b = (fun _ => false) := by
  funext i
  show xor (b i) (b i) = false
  cases b i <;> rfl

/-- Seat-level composition: the seat set of `b₁ + b₂` is
the symmetric difference of the seat sets of `b₁` and
`b₂` — the four seat pairs are disjoint, so no seat is
ever toggled by two different bits. Proved by the
32-seat case split. -/
theorem toggled_bitsAdd (b₁ b₂ : Fin 4 → Bool) (i : Fin 32) :
    toggled (bitsAdd b₁ b₂) i
      = xor (toggled b₁ i) (toggled b₂ i) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [toggled, bitsAdd]

/-- **The composition law (headline, CLS-2G):**
`T_{b₁ + b₂} = T_{b₁} ∘ T_{b₂}` as maps on
representations. -/
theorem toggleMap_bitsAdd (b₁ b₂ : Fin 4 → Bool) :
    toggleMap (bitsAdd b₁ b₂)
      = toggleMap b₁ ∘ toggleMap b₂ := by
  funext π a i j
  show (if toggled (bitsAdd b₁ b₂) i = true ∧ i = j
      then star (π a i j) else π a i j)
    = (if toggled b₁ i = true ∧ i = j
        then star (if toggled b₂ i = true ∧ i = j
          then star (π a i j) else π a i j)
        else (if toggled b₂ i = true ∧ i = j
          then star (π a i j) else π a i j))
  rw [toggled_bitsAdd]
  cases h1 : toggled b₁ i <;> cases h2 : toggled b₂ i <;>
    by_cases hij : i = j <;> simp [h1, h2, hij, star_star]

/-! ## §2. Corollaries of the composition law -/

/-- Corollary: `T_0 = id`. -/
theorem toggleMap_zero :
    toggleMap (fun _ => false) = id := by
  funext π a i j
  show (if toggled (fun _ => false) i = true ∧ i = j
      then star (π a i j) else π a i j) = π a i j
  have ht : toggled (fun _ => false) i = false := by
    simp [toggled]
  simp [ht]

/-- Corollary: every toggle is involutive,
`T_b ∘ T_b = id`. -/
theorem toggleMap_involutive (b : Fin 4 → Bool) :
    Function.Involutive (toggleMap b) := by
  intro π
  have h := toggleMap_bitsAdd b b
  rw [bitsAdd_self, toggleMap_zero] at h
  exact congrFun h.symm π

/-- Corollary: toggles commute in general. -/
theorem toggleMap_comm (b₁ b₂ : Fin 4 → Bool) :
    toggleMap b₁ ∘ toggleMap b₂
      = toggleMap b₂ ∘ toggleMap b₁ := by
  rw [← toggleMap_bitsAdd, ← toggleMap_bitsAdd, bitsAdd_comm]

/-- Corollary: distinct single-bit toggles commute. -/
theorem toggleMap_bitPat_commute {k l : Fin 4} (_ : k ≠ l) :
    toggleMap (bitPat k) ∘ toggleMap (bitPat l)
      = toggleMap (bitPat l) ∘ toggleMap (bitPat k) :=
  toggleMap_comm _ _

/-! ## §3. Entry lemmas for the orbit read-back -/

theorem pi1_dSeat_diag (c : Fin 3) (a : AF) :
    pi1 a (dSeat c) (dSeat c) = star a.u1 := by
  have h := pi1_entry_quarkR a c c ⟨1, by omega⟩ ⟨1, by omega⟩
  have hd : (⟨10 + 2 * c.val + (⟨1, by omega⟩ : Fin 2).val,
      by have hc := c.isLt; omega⟩ : Fin 32) = dSeat c :=
    Fin.ext (by show 10 + 2 * c.val + 1 = 11 + 2 * c.val; omega)
  rw [hd] at h
  simpa using h

theorem orbitCorrD_s8_diag (a : AF) :
    orbitCorrD a s8 s8 = star a.u1 - a.u1 := by
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (by decide : ¬ (s9 = s8 ∧ s9 = s8)), add_zero]

theorem orbitCorrS_s8 (c : Fin 3) (a : AF) :
    orbitCorrS c a s8 s8 = 0 := by
  have hu : ¬ (uSeat c = s8 ∧ uSeat c = s8) := by
    intro h
    have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv
    have hc := c.isLt
    omega
  have hd : ¬ (dSeat c = s8 ∧ dSeat c = s8) := by
    intro h
    have hv := congrArg Fin.val h.1
    simp only [dSeat] at hv
    have hc := c.isLt
    omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem orbitCorrD_dSeat (c : Fin 3) (a : AF) :
    orbitCorrD a (dSeat c) (dSeat c) = 0 := by
  have h8 : ¬ (s8 = dSeat c ∧ s8 = dSeat c) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [dSeat] at hv; have hc := c.isLt; omega
  have h9 : ¬ (s9 = dSeat c ∧ s9 = dSeat c) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [dSeat] at hv; have hc := c.isLt; omega
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg h8, if_neg h9, add_zero]

theorem orbitCorrS_dSeat_diag (c : Fin 3) (a : AF) :
    orbitCorrS c a (dSeat c) (dSeat c) = a.u1 - star a.u1 := by
  have hu : ¬ (uSeat c = dSeat c ∧ uSeat c = dSeat c) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [uSeat, dSeat] at hv; omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_pos ⟨rfl, rfl⟩,
    zero_add]

theorem orbitCorrS_dSeat_of_ne (c c' : Fin 3) (h : c' ≠ c)
    (a : AF) : orbitCorrS c' a (dSeat c) (dSeat c) = 0 := by
  have hu : ¬ (uSeat c' = dSeat c ∧ uSeat c' = dSeat c) := by
    intro hh; have hv := congrArg Fin.val hh.1
    simp only [uSeat, dSeat] at hv; have hc := c'.isLt; omega
  have hd : ¬ (dSeat c' = dSeat c ∧ dSeat c' = dSeat c) := by
    intro hh; apply h
    have hv := congrArg Fin.val hh.1
    simp only [dSeat] at hv
    exact Fin.ext (by omega)
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem orbitRep_dSeat_diag (b : Fin 4 → Bool) (c : Fin 3)
    (a : AF) :
    orbitRep b a (dSeat c) (dSeat c)
      = if b (swapIdx c) then a.u1 else star a.u1 := by
  fin_cases c <;>
    (show (pi1 a + (if b 0 then orbitCorrD a else 0)
        + (if b 1 then orbitCorrS 0 a else 0)
        + (if b 2 then orbitCorrS 1 a else 0)
        + (if b 3 then orbitCorrS 2 a else 0)) _ _
      = _; by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
      by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
      simp [Matrix.add_apply, h0, h1, h2, h3, pi1_dSeat_diag,
        orbitCorrD_dSeat, orbitCorrS_dSeat_diag,
        orbitCorrS_dSeat_of_ne, swapIdx] <;> ring)

theorem orbitCorrD_diag_of_ne {i : Fin 32} (h8 : i ≠ s8)
    (h9 : i ≠ s9) (a : AF) : orbitCorrD a i i = 0 := by
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply,
    if_neg (fun h => h8 h.1.symm),
    if_neg (fun h => h9 h.1.symm), add_zero]

theorem orbitCorrS_diag_of_ne {i : Fin 32} (c : Fin 3)
    (hu : i ≠ uSeat c) (hd : i ≠ dSeat c) (a : AF) :
    orbitCorrS c a i i = 0 := by
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply,
    if_neg (fun h => hu h.1.symm),
    if_neg (fun h => hd h.1.symm), add_zero]

theorem toggled_s8 (b : Fin 4 → Bool) : toggled b s8 = b 0 := by
  simp [toggled]

theorem toggled_s9 (b : Fin 4 → Bool) : toggled b s9 = b 0 := by
  simp [toggled]

theorem toggled_uSeat (b : Fin 4 → Bool) (c : Fin 3) :
    toggled b (uSeat c) = b (swapIdx c) := by
  fin_cases c <;> simp [toggled, uSeat, swapIdx]

theorem toggled_dSeat (b : Fin 4 → Bool) (c : Fin 3) :
    toggled b (dSeat c) = b (swapIdx c) := by
  fin_cases c <;> simp [toggled, dSeat, swapIdx]

theorem toggled_eq_false_of_not_seat {i : Fin 32}
    (h8 : i.val ≠ 8) (h9 : i.val ≠ 9) (h10 : i.val ≠ 10)
    (h11 : i.val ≠ 11) (h12 : i.val ≠ 12) (h13 : i.val ≠ 13)
    (h14 : i.val ≠ 14) (h15 : i.val ≠ 15) (b : Fin 4 → Bool) :
    toggled b i = false := by
  simp [toggled, h8, h9, h10, h11, h12, h13, h14, h15]

/-! ## §4. The orbit is the image of the action -/

/-- **The orbit read-back (headline, CLS-2G):**
`orbitRep b = T_b pi1` — the landed orbit representative
is the toggle action of `b` on `pi1`. -/
theorem orbitRep_eq_toggleMap (b : Fin 4 → Bool) :
    orbitRep b = toggleMap b pi1 := by
  funext a
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h8 : i = s8
    · subst h8
      have ht : toggled b s8 = b 0 := toggled_s8 b
      have hpi : pi1 a s8 s8 = a.u1 := pi1_entry_nuR a
      show orbitRep b a s8 s8
        = (if toggled b s8 = true ∧ s8 = s8
            then star (pi1 a s8 s8) else pi1 a s8 s8)
      by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
        by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
        simp [Matrix.add_apply, ht, h0, h1, h2, h3, hpi, orbitRep,
          orbitCorrD_s8_diag, orbitCorrS_s8] <;> ring
    · by_cases h9 : i = s9
      · subst h9
        have ht : toggled b s9 = b 0 := toggled_s9 b
        have hpi : pi1 a s9 s9 = star a.u1 := pi1_entry_eR a
        show orbitRep b a s9 s9
          = (if toggled b s9 = true ∧ s9 = s9
              then star (pi1 a s9 s9) else pi1 a s9 s9)
        rw [orbitRep_s9_diag]
        by_cases h0 : b 0 <;> simp [ht, h0, hpi, star_star]
      · by_cases hu0 : i = uSeat 0
        · subst hu0
          have ht : toggled b (uSeat 0) = b (swapIdx 0) :=
            toggled_uSeat b 0
          have hpi : pi1 a (uSeat 0) (uSeat 0) = a.u1 :=
            pi1_uSeat_diag 0 a
          show orbitRep b a (uSeat 0) (uSeat 0)
            = (if toggled b (uSeat 0) = true ∧ uSeat 0 = uSeat 0
                then star (pi1 a (uSeat 0) (uSeat 0))
                else pi1 a (uSeat 0) (uSeat 0))
          rw [orbitRep_uSeat_diag]
          by_cases hb : b (swapIdx 0) <;> simp [ht, hb, hpi]
        · by_cases hd0 : i = dSeat 0
          · subst hd0
            have ht : toggled b (dSeat 0) = b (swapIdx 0) :=
              toggled_dSeat b 0
            have hpi : pi1 a (dSeat 0) (dSeat 0) = star a.u1 :=
              pi1_dSeat_diag 0 a
            show orbitRep b a (dSeat 0) (dSeat 0)
              = (if toggled b (dSeat 0) = true ∧ dSeat 0 = dSeat 0
                  then star (pi1 a (dSeat 0) (dSeat 0))
                  else pi1 a (dSeat 0) (dSeat 0))
            rw [orbitRep_dSeat_diag]
            by_cases hb : b (swapIdx 0) <;>
              simp [ht, hb, hpi, star_star]
          · by_cases hu1 : i = uSeat 1
            · subst hu1
              have ht : toggled b (uSeat 1) = b (swapIdx 1) :=
                toggled_uSeat b 1
              have hpi : pi1 a (uSeat 1) (uSeat 1) = a.u1 :=
                pi1_uSeat_diag 1 a
              show orbitRep b a (uSeat 1) (uSeat 1)
                = (if toggled b (uSeat 1) = true
                    ∧ uSeat 1 = uSeat 1
                    then star (pi1 a (uSeat 1) (uSeat 1))
                    else pi1 a (uSeat 1) (uSeat 1))
              rw [orbitRep_uSeat_diag]
              by_cases hb : b (swapIdx 1) <;> simp [ht, hb, hpi]
            · by_cases hd1 : i = dSeat 1
              · subst hd1
                have ht : toggled b (dSeat 1) = b (swapIdx 1) :=
                  toggled_dSeat b 1
                have hpi : pi1 a (dSeat 1) (dSeat 1)
                    = star a.u1 :=
                  pi1_dSeat_diag 1 a
                show orbitRep b a (dSeat 1) (dSeat 1)
                  = (if toggled b (dSeat 1) = true
                      ∧ dSeat 1 = dSeat 1
                      then star (pi1 a (dSeat 1) (dSeat 1))
                      else pi1 a (dSeat 1) (dSeat 1))
                rw [orbitRep_dSeat_diag]
                by_cases hb : b (swapIdx 1) <;>
                  simp [ht, hb, hpi, star_star]
              · by_cases hu2 : i = uSeat 2
                · subst hu2
                  have ht : toggled b (uSeat 2)
                      = b (swapIdx 2) :=
                    toggled_uSeat b 2
                  have hpi : pi1 a (uSeat 2) (uSeat 2) = a.u1 :=
                    pi1_uSeat_diag 2 a
                  show orbitRep b a (uSeat 2) (uSeat 2)
                    = (if toggled b (uSeat 2) = true
                        ∧ uSeat 2 = uSeat 2
                        then star (pi1 a (uSeat 2) (uSeat 2))
                        else pi1 a (uSeat 2) (uSeat 2))
                  rw [orbitRep_uSeat_diag]
                  by_cases hb : b (swapIdx 2) <;>
                    simp [ht, hb, hpi]
                · by_cases hd2 : i = dSeat 2
                  · subst hd2
                    have ht : toggled b (dSeat 2)
                        = b (swapIdx 2) :=
                      toggled_dSeat b 2
                    have hpi : pi1 a (dSeat 2) (dSeat 2)
                        = star a.u1 :=
                      pi1_dSeat_diag 2 a
                    show orbitRep b a (dSeat 2) (dSeat 2)
                      = (if toggled b (dSeat 2) = true
                          ∧ dSeat 2 = dSeat 2
                          then star (pi1 a (dSeat 2) (dSeat 2))
                          else pi1 a (dSeat 2) (dSeat 2))
                    rw [orbitRep_dSeat_diag]
                    by_cases hb : b (swapIdx 2) <;>
                      simp [ht, hb, hpi, star_star]
                  · -- Generic diagonal seat: no bit owns it.
                    have hv8 : i.val ≠ 8 := fun hv => h8 (Fin.ext hv)
                    have hv9 : i.val ≠ 9 := fun hv => h9 (Fin.ext hv)
                    have hv10 : i.val ≠ 10 :=
                      fun hv => hu0 (Fin.ext hv)
                    have hv11 : i.val ≠ 11 :=
                      fun hv => hd0 (Fin.ext hv)
                    have hv12 : i.val ≠ 12 :=
                      fun hv => hu1 (Fin.ext hv)
                    have hv13 : i.val ≠ 13 :=
                      fun hv => hd1 (Fin.ext hv)
                    have hv14 : i.val ≠ 14 :=
                      fun hv => hu2 (Fin.ext hv)
                    have hv15 : i.val ≠ 15 :=
                      fun hv => hd2 (Fin.ext hv)
                    have ht : toggled b i = false :=
                      toggled_eq_false_of_not_seat hv8 hv9 hv10
                        hv11 hv12 hv13 hv14 hv15 b
                    show orbitRep b a i i
                      = (if toggled b i = true ∧ i = i
                          then star (pi1 a i i) else pi1 a i i)
                    by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
                      by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
                      simp [Matrix.add_apply, ht, h0, h1, h2, h3,
                        orbitRep, orbitCorrD_diag_of_ne h8 h9,
                        orbitCorrS_diag_of_ne (c := 0) hu0 hd0,
                        orbitCorrS_diag_of_ne (c := 1) hu1 hd1,
                        orbitCorrS_diag_of_ne (c := 2) hu2 hd2]
  · -- Off-diagonal: corrections are diagonal singles.
    have hsingle : ∀ (s : Fin 32) (x : ℂ),
        Matrix.single s s x i j = 0 := by
      intro s x
      rw [Matrix.single_apply]
      exact if_neg (fun h => hij (h.1.symm.trans h.2))
    show orbitRep b a i j
      = (if toggled b i = true ∧ i = j
          then star (pi1 a i j) else pi1 a i j)
    by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
      by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
      simp [Matrix.add_apply, hij, h0, h1, h2, h3, orbitRep,
        orbitCorrD, orbitCorrS, hsingle]

/-- The action transports along the orbit:
`orbitRep (b₁ + b₂) = T_{b₁} (orbitRep b₂)`. -/
theorem orbitRep_bitsAdd (b₁ b₂ : Fin 4 → Bool) :
    orbitRep (bitsAdd b₁ b₂) = toggleMap b₁ (orbitRep b₂) := by
  rw [orbitRep_eq_toggleMap, orbitRep_eq_toggleMap,
    toggleMap_bitsAdd]
  rfl

/-- **CLS-2G assembled:** the orbit is the image of a
group action of (ℤ/2)⁴ — composition, the read-back
`orbitRep b = T_b pi1`, and `T_0 = id`. -/
theorem orbit_group_action :
    (∀ b₁ b₂ : Fin 4 → Bool,
      toggleMap (bitsAdd b₁ b₂)
        = toggleMap b₁ ∘ toggleMap b₂)
    ∧ (∀ b : Fin 4 → Bool, orbitRep b = toggleMap b pi1)
    ∧ toggleMap (fun _ => false) = id :=
  ⟨toggleMap_bitsAdd, orbitRep_eq_toggleMap, toggleMap_zero⟩

#print axioms toggled_bitsAdd
#print axioms toggleMap_bitsAdd
#print axioms toggleMap_zero
#print axioms toggleMap_involutive
#print axioms toggleMap_bitPat_commute
#print axioms orbitRep_eq_toggleMap
#print axioms orbitRep_bitsAdd
#print axioms orbit_group_action

end ThetLogos.DialOneSwapOrbitGroupLaw
