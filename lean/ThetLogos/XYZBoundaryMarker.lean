import ThetLogos.XYZTripotents

/-!
# ThetLogos.XYZBoundaryMarker — XYZ-2: the boundary marker (T3 marker; T5 question OPEN)

This module lands brick **XYZ-2** from the XYZ campaign (scoping §4): the
**boundary marker** for rubric rule **R5**, the entry-ring trap of
`ThetLogos.XYZTripotents` §14. It is a **kill of a kill-route**, recorded
at the same volume as a win:

- R5 (`no_gaussInt_triple_reaches_genM7`) kills every triple of
  Gaussian-integer-valued (`ℤ[i]`-valued) matrices at `smGen 11 = genM 7`,
  because `genM 7` carries the entry `1/√3` at (18, 18)
  (`genM_seven_18_18`), which is not a Gaussian integer
  (`not_gaussInt_inv_sqrt3`). XYZ-1 (`ThetLogos.XYZPoolKill`) used R5 to
  close the entire named pool of sixteen tripotents.
- **That route cannot be extended to the question
  `xyz_tripotents_exist`.** This module constructs one explicit
  tripotent `tripT` — a rank-one partial isometry, below — whose entry
  at (18, 18) is exactly `1/√3`, and proves `Tripotent tripT` by direct
  entry computation. Hence R5's hypothesis (`∀ i j, IsGaussInt (T i j)`)
  is *false* for `tripT` (`r5_hypotheses_fail_for_tripT`): no triple
  containing `tripT` can be fed to R5 at all. The ℤ[i] species boundary
  is a theorem, not an impression: tripotents outside the ℤ[i] species
  exist, so no entry-ring argument at the ℤ[i] ring — and, by the same
  shape, at any proper star-closed subring a future wave might name —
  can by itself close the question. Any future "generalize R5" brick is
  dead on arrival; this marker is the receipt.

**The concrete tripotent, as data.** The triplet is the M-sector colour
triplet `T₀ = (18, 20, 22)`, i.e. `(tripletIdx 0 0, tripletIdx 0 1,
tripletIdx 0 2)` in `tripletOf`'s enumeration. The vectors are

- `u = e₁₈`, the unit vector at the first triplet position;
- `v = (1, 1, 1)/√3` on the triplet positions (18, 20, 22), zero
  elsewhere — the triplet-normalized vector.

`tripT = u vᴴ`: its only nonzero row is row 18, with the three entries
`tripT 18 18 = tripT 18 20 = tripT 18 22 = 1/√3` (all real, so the
conjugate transpose is entrywise plain). It is a rank-one partial
isometry: `tripT * tripTᴴ` is the support projector `tripE = E₁₈,₁₈`,
and `tripE * tripT = tripT`, which is the tripotency computation of §2.

**Honest rubric interaction (R1–R4), checked for triples containing
`tripT`.** The marker claims only the R5 boundary; the other landed
rules were checked against `tripT` itself and the answer is mixed:

- **R1 (diagonal trap) cannot touch any triple containing `tripT`:**
  `tripT` is not diagonal — its (18, 20) entry is `1/√3 ≠ 0`
  (`tripT_not_diagonal`) — while R1's hypothesis needs *every* member
  diagonal.
- **R2 (conjugation trap)** is a closure fact about conjugates of
  diagonal tripotents; those conjugates are diagonal, and `tripT` is
  not, so no R2 family contains `tripT` either.
- **R4 (pair-support trap) cannot touch any triple containing
  `tripT`:** pair support is a per-member hypothesis, and `tripT`
  violates it at (18, 20): `20 ≠ 18` and `20 ≠ partner 18 = 2`
  (`tripT_not_pairSupported`).
- **R3 (support trap) is different in kind and stays honestly open
  per-triple:** `memGenTRO_supported` is fully general — it kills a
  *particular* triple whenever all three members share one restrictive
  index support that some generator escapes. Nothing landed instances
  R3 against `tripT`, and R3 gives no species-level exclusion of
  `tripT` (a co-member with full support breaks any common bound);
  but a specific triple `{tripT, Y, Z}` whose `Y, Z` happen to share a
  restrictive support with `tripT` could still die by R3. The marker
  claims nothing there.

**Role and fences.** `tripT` is a **candidate ingredient** for XYZ-3's
live families (its conjugates/permutations are on XYZ-3's candidate
list). **No generation claim is made or implied for `tripT` alone** —
no triple is exhibited here, no membership in any generated TRO is
asserted, and `xyz_tripotents_exist` stays **OPEN**. NO CLAIM; dials
0/4, nowhere moved. Tier T3 (machine-checked) for the marker itself;
the underlying question remains T5/open.
-/

namespace ThetLogos

/-! ## §1. The concrete tripotent, as data -/

/-- The exhibiting scalar: `1/√3` as a complex number, in exactly the
    form carried by `genM 7` at (18, 18) (`genM_seven_18_18`). Tier T2. -/
noncomputable def tripS : ℂ := (((Real.sqrt 3 : ℝ) : ℂ))⁻¹

/-- The boundary-marker tripotent: the rank-one partial isometry
    `u vᴴ` with `u = e₁₈` and `v = (1, 1, 1)/√3` on the M-sector colour
    triplet `T₀ = (18, 20, 22)` (triplet 0 of `tripletOf`). Only row 18
    is nonzero; its three triplet entries are each exactly `1/√3`.
    Tier T2. -/
noncomputable def tripT : Matrix I32 I32 ℂ := fun i j =>
  if i.val = 18 ∧ (j.val = 18 ∨ j.val = 20 ∨ j.val = 22) then tripS else 0

/-- The support projector of `tripT`: the matrix unit `E₁₈,₁₈`.
    Tier T2. -/
noncomputable def tripE : Matrix I32 I32 ℂ := fun i j =>
  if i.val = 18 ∧ j.val = 18 then (1 : ℂ) else 0

/-- Entry of `tripT` on its support: row 18, triplet column. Tier T3. -/
theorem tripT_apply_of (i j : I32) (hi : i.val = 18)
    (hj : j.val = 18 ∨ j.val = 20 ∨ j.val = 22) : tripT i j = tripS :=
  if_pos ⟨hi, hj⟩

/-- Entry of `tripT` off its support is zero. Tier T3. -/
theorem tripT_apply_of_not (i j : I32)
    (h : ¬ (i.val = 18 ∧ (j.val = 18 ∨ j.val = 20 ∨ j.val = 22))) :
    tripT i j = 0 :=
  if_neg h

/-- The exhibiting entry: `tripT` at (18, 18) is exactly `1/√3`, in the
    same closed form as `genM_seven_18_18`. Tier T3. -/
theorem tripT_entry_18_18 :
    tripT (⟨18, by norm_num⟩ : I32) (⟨18, by norm_num⟩ : I32) =
    (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ :=
  tripT_apply_of _ _ rfl (Or.inl rfl)

/-- The off-diagonal triplet entry: `tripT` at (18, 20) is `1/√3`.
    Tier T3. -/
theorem tripT_entry_18_20 :
    tripT (⟨18, by norm_num⟩ : I32) (⟨20, by norm_num⟩ : I32) = tripS :=
  tripT_apply_of _ _ rfl (Or.inr (Or.inl rfl))

/-- The triplet entry in `tripletIdx` coordinates: (18, 18) is
    `(tripletIdx 0 0, tripletIdx 0 0)`. Tier T3. -/
theorem tripT_triplet_entry :
    tripT (tripletIdx 0 0) (tripletIdx 0 0) = tripS := by
  have h : tripletIdx (0 : Fin 4) (0 : Fin 3) = (⟨18, by norm_num⟩ : I32) := by
    decide
  rw [h]
  exact tripT_apply_of _ _ rfl (Or.inl rfl)

/-! ## §2. Scalar facts about `1/√3` -/

/-- `1/√3` is a real scalar: `star` fixes it. Tier T3. -/
theorem tripS_star : star tripS = tripS := by
  unfold tripS
  rw [star_inv₀]
  simp

/-- `1/√3 ≠ 0`. Tier T3. -/
theorem tripS_ne_zero : tripS ≠ 0 := by
  unfold tripS
  exact inv_ne_zero (by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 3))

/-- Real norm identity: `(√3)⁻¹ · (√3)⁻¹ = 3⁻¹`. Tier T3. -/
theorem inv_sqrt3_mul_self : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]

/-- The norm computation of the partial isometry: `(1/√3) · star (1/√3)
    = 1/3`. Tier T3. -/
theorem tripS_mul_star : tripS * star tripS = ((3 : ℝ) : ℂ)⁻¹ := by
  have hcast : (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ = (((Real.sqrt 3)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
  rw [tripS_star]
  unfold tripS
  rw [hcast, ← Complex.ofReal_mul, inv_sqrt3_mul_self, Complex.ofReal_inv]

/-- Three copies of the norm: `(1/3) + (1/3) + (1/3) = 1` in ℂ,
    stated in the cast form produced by the entry sum. Tier T3. -/
theorem three_mul_tripS_norm :
    ((3 : ℝ) : ℂ)⁻¹ + ((3 : ℝ) : ℂ)⁻¹ + ((3 : ℝ) : ℂ)⁻¹ = 1 := by
  have hr : (3 : ℝ)⁻¹ + (3 : ℝ)⁻¹ + (3 : ℝ)⁻¹ = 1 := by norm_num
  rw [← Complex.ofReal_inv, ← Complex.ofReal_add, ← Complex.ofReal_add, hr]
  exact Complex.ofReal_one

/-! ## §3. Tripotency by direct entry computation -/

/-- Entry of `tripE` on its support. Tier T3. -/
theorem tripE_apply_of (i j : I32) (hi : i.val = 18) (hj : j.val = 18) :
    tripE i j = 1 :=
  if_pos ⟨hi, hj⟩

/-- Entry of `tripE` off its support is zero. Tier T3. -/
theorem tripE_apply_of_not (i j : I32) (h : ¬ (i.val = 18 ∧ j.val = 18)) :
    tripE i j = 0 :=
  if_neg h

/-- First half of the partial-isometry computation:
    `tripT * tripTᴴ = tripE`. Entrywise: off row/column 18 every summand
    vanishes; at (18, 18) the sum over the triplet (18, 20, 22) is
    `3 · (1/√3 · star (1/√3)) = 3 · (1/3) = 1`. Tier T3. -/
theorem tripT_mul_conjTranspose : tripT * tripT.conjTranspose = tripE := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val = 18
  · by_cases hj : j.val = 18
    · -- At (18, 18): restrict the sum to the triplet finset.
      have hterm : ∀ k : I32, k.val = 18 ∨ k.val = 20 ∨ k.val = 22 →
          tripT i k * tripT.conjTranspose k j = tripS * star tripS := by
        intro k hk
        rw [Matrix.conjTranspose_apply, tripT_apply_of i k hi hk,
          tripT_apply_of j k hj hk]
      have hsum : (∑ k : I32, tripT i k * tripT.conjTranspose k j)
          = ∑ k ∈ ({⟨18, by norm_num⟩, ⟨20, by norm_num⟩, ⟨22, by norm_num⟩} :
              Finset I32), tripT i k * tripT.conjTranspose k j := by
        apply (Finset.sum_subset (Finset.subset_univ _) _).symm
        intro k _ hk
        have hkv : ¬ (k.val = 18 ∨ k.val = 20 ∨ k.val = 22) := by
          intro hkd
          apply hk
          rcases hkd with h | h | h
          · exact Finset.mem_insert.mpr (Or.inl (Fin.ext h))
          · exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl (Fin.ext h))))
          · exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_singleton.mpr (Fin.ext h)))))
        rw [tripT_apply_of_not i k (fun hc => hkv hc.2), zero_mul]
      rw [hsum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton, hterm _ (Or.inl rfl),
        hterm _ (Or.inr (Or.inl rfl)), hterm _ (Or.inr (Or.inr rfl)),
        tripE_apply_of i j hi hj, tripS_mul_star, ← add_assoc]
      exact three_mul_tripS_norm
    · -- Column off 18: every `star (tripT j k)` vanishes.
      rw [Finset.sum_eq_zero]
      · exact (tripE_apply_of_not i j (fun h => hj h.2)).symm
      · intro k _
        rw [Matrix.conjTranspose_apply,
          tripT_apply_of_not j k (fun h => hj h.1), star_zero, mul_zero]
  · -- Row off 18: every `tripT i k` vanishes.
    rw [Finset.sum_eq_zero]
    · exact (tripE_apply_of_not i j (fun h => hi h.1)).symm
    · intro k _
      rw [tripT_apply_of_not i k (fun h => hi h.1), zero_mul]

/-- Second half: the support projector acts trivially on `tripT`,
    `tripE * tripT = tripT`. Entrywise the sum collapses to the single
    index `k = 18`. Tier T3. -/
theorem tripE_mul_tripT : tripE * tripT = tripT := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨18, by norm_num⟩ : I32)]
  · by_cases hi : i.val = 18
    · have hii : i = (⟨18, by norm_num⟩ : I32) := Fin.ext hi
      rw [tripE_apply_of i _ hi rfl, one_mul, hii]
    · rw [tripE_apply_of_not i _ (fun h => hi h.1), zero_mul,
        tripT_apply_of_not i j (fun h => hi h.1)]
  · intro k _ hk
    have hkv : k.val ≠ 18 := fun h => hk (Fin.ext h)
    rw [tripE_apply_of_not i k (fun h => hkv h.2), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The boundary marker is a tripotent.** `Tripotent tripT`, proved by
    the direct entry computation above, following the corpus's
    `Tripotent` definition (`ternaryMat T T T = T`, i.e.
    `T * Tᴴ * T = T`) literally. Tier T3. -/
theorem tripotent_tripT : Tripotent tripT := by
  unfold Tripotent ternaryMat
  rw [tripT_mul_conjTranspose, tripE_mul_tripT]

/-! ## §4. The boundary fact: R5 cannot exclude `tripT` -/

/-- The exhibiting entry of `tripT` is not a Gaussian integer, by the
    landed `not_gaussInt_inv_sqrt3`. Tier T3. -/
theorem tripT_entry_not_gaussInt :
    ¬ IsGaussInt (tripT (⟨18, by norm_num⟩ : I32) (⟨18, by norm_num⟩ : I32)) := by
  rw [tripT_entry_18_18]
  exact not_gaussInt_inv_sqrt3

/-- R5's hypothesis fails for `tripT`: its entries are not all Gaussian
    integers. Tier T3. -/
theorem r5_hypothesis_fails_for_tripT : ¬ ∀ i j, IsGaussInt (tripT i j) :=
  fun h => tripT_entry_not_gaussInt (h _ _)

/-- **The boundary marker, stated plainly.** For any `Y, Z`, the three
    Gaussian-integer hypotheses of R5 (`no_gaussInt_triple_reaches_genM7`)
    cannot jointly hold for the triple `(tripT, Y, Z)`: the R5 route
    cannot be extended to exclude `tripT`. `tripT` is a tripotent
    (`tripotent_tripT`) outside the ℤ[i] species. This kills the
    *kill-route's extension*, not the question: `xyz_tripotents_exist`
    stays open, and no generation claim is made for `tripT`. Tier T3. -/
theorem r5_cannot_exclude_tripT (Y Z : Matrix I32 I32 ℂ) :
    ¬ ((∀ i j, IsGaussInt (tripT i j)) ∧ (∀ i j, IsGaussInt (Y i j)) ∧
      (∀ i j, IsGaussInt (Z i j))) :=
  fun h => r5_hypothesis_fails_for_tripT h.1

/-! ## §5. Honest R1/R4 interaction: those routes cannot use `tripT` either -/

/-- R1 interaction: `tripT` is not diagonal — the (18, 20) entry is
    `1/√3 ≠ 0` — so no all-diagonal triple (R1's hypothesis) contains
    `tripT`. Tier T3. -/
theorem tripT_not_diagonal : ¬ ∃ d : I32 → ℂ, tripT = Matrix.diagonal d := by
  rintro ⟨d, hd⟩
  have h := congrArg (fun M : Matrix I32 I32 ℂ =>
    M (⟨18, by norm_num⟩ : I32) (⟨20, by norm_num⟩ : I32)) hd
  rw [tripT_entry_18_20, Matrix.diagonal_apply_ne _
    (by decide : (⟨18, by norm_num⟩ : I32) ≠ ⟨20, by norm_num⟩)] at h
  exact tripS_ne_zero h

/-- R4 interaction: `tripT` does not have pair support — at (18, 20) the
    entry is nonzero, but `20 ≠ 18` and `20 ≠ partner 18 = 2` — so R4's
    per-member hypothesis fails for every triple containing `tripT`.
    Tier T3. -/
theorem tripT_not_pairSupported :
    ¬ ∀ i j : I32, tripT i j ≠ 0 → i = j ∨ j = partner i := by
  intro h
  have hne : tripT (⟨18, by norm_num⟩ : I32) (⟨20, by norm_num⟩ : I32) ≠ 0 := by
    rw [tripT_entry_18_20]
    exact tripS_ne_zero
  rcases h _ _ hne with h1 | h2
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)

end ThetLogos
