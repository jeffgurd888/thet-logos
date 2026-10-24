import ThetLogos.LatticeOSSpace

/-!
# LatticeOSMarginal — the `posToSlice` marginal identity

**NO CLAIM.** Parts of the official Clay Yang–Mills statement
closed by this module: 0.

`LatticeOSSpace` (§7, `osForm_slice_nonneg_of_gramClause`)
named one loose end in its own text: the transfer of
measurability between the slice measure and the product measure
on the strict positive half is the **`posToSlice` marginal
identity** — the pushforward of the product Haar measure on
`posLinks` configurations under the slice coordinatization
`posToSlice` is the product Haar measure on the slice —
recorded there as unproved (priced S) and explicitly NOT used
by the landed theorems. This module proves it (gap-theorem
queue, 2026-10-24, item Q1). The transfer-matrix charter
(`whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`
§2) notes its R1/R3 rungs may consume it.

The proof is the standard marginal computation: the two
measures agree on rectangles (Mathlib's `Measure.pi_eq`);
the preimage of a slice rectangle under `posToSlice` is the
rectangle over `posLinks` carrying the same side sets on the
slice coordinates and the whole space off them, and the
product over `posLinks` then collapses to the product over
the slice since `μG` is a probability measure.

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  The marginal identity `posToSlice_map_measurePi` and its
  `sliceMeasure` form `posToSlice_map_sliceMeasure` are
  machine-checked (parent-verified rebuild, 3,551 jobs;
  axioms standard, no `sorryAx`). Dossier:
  `whitepaper/gap-queue-q1-postoslice-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Set

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The coordinate inclusion of the slice links into the
strict positive half's links — the index map `posToSlice`
precomposes with. -/
def sliceIncl (hN : Even N) :
    ↥(sliceLinks (N := N)) → ↥(posLinks (N := N)) :=
  fun ℓ => ⟨ℓ.1, sliceLinks_subset_posLinks hN ℓ.2⟩

theorem sliceIncl_injective (hN : Even N) :
    Function.Injective (sliceIncl hN) := by
  intro a b h
  have h1 : (sliceIncl hN a).1 = (sliceIncl hN b).1 :=
    congrArg (fun ℓ : ↥(posLinks (N := N)) => ℓ.1) h
  exact Subtype.ext h1

/-- `posToSlice` is precomposition with `sliceIncl`. -/
theorem posToSlice_eq (hN : Even N) :
    posToSlice (G := G) hN
      = fun y ℓ => y (sliceIncl hN ℓ) :=
  rfl

/-- The set of `posLinks` side sets a slice rectangle pulls
back to: the given side set on slice coordinates, the whole
space off them. -/
noncomputable def rectExtend (hN : Even N)
    (s : ↥(sliceLinks (N := N)) → Set G) :
    ↥(posLinks (N := N)) → Set G :=
  fun k => if h : ∃ ℓ, sliceIncl hN ℓ = k then s (Classical.choose h)
    else Set.univ

theorem rectExtend_sliceIncl (hN : Even N)
    (s : ↥(sliceLinks (N := N)) → Set G) (ℓ : ↥(sliceLinks (N := N))) :
    rectExtend (G := G) hN s (sliceIncl hN ℓ) = s ℓ := by
  have hex : ∃ ℓ', sliceIncl hN ℓ' = sliceIncl hN ℓ := ⟨ℓ, rfl⟩
  have hchoose : Classical.choose hex = ℓ :=
    sliceIncl_injective hN (Classical.choose_spec hex)
  unfold rectExtend
  rw [dif_pos hex, hchoose]

theorem rectExtend_of_not_mem (hN : Even N)
    (s : ↥(sliceLinks (N := N)) → Set G)
    {k : ↥(posLinks (N := N))}
    (hk : k ∉ Set.range (sliceIncl hN)) :
    rectExtend (G := G) hN s k = Set.univ := by
  unfold rectExtend
  exact dif_neg (by simpa [Set.mem_range] using hk)

/-- The preimage of a slice rectangle under `posToSlice` is
the extended rectangle over `posLinks`. -/
theorem posToSlice_preimage_pi (hN : Even N)
    (s : ↥(sliceLinks (N := N)) → Set G) :
    posToSlice (G := G) hN ⁻¹' (Set.pi Set.univ s)
      = Set.pi Set.univ (rectExtend (G := G) hN s) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_const]
  constructor
  · intro hy k
    by_cases hk : ∃ ℓ, sliceIncl hN ℓ = k
    · obtain ⟨ℓ, rfl⟩ := hk
      rw [rectExtend_sliceIncl]
      exact hy ℓ
    · rw [rectExtend_of_not_mem _ _ (by
        simpa [Set.mem_range] using hk)]
      trivial
  · intro hy ℓ
    have := hy (sliceIncl hN ℓ)
    rwa [rectExtend_sliceIncl] at this

/-- The product of the extended side sets' measures over
`posLinks` collapses to the product over the slice: off the
slice coordinates every factor is `μG univ = 1`. -/
theorem prod_rectExtend (hN : Even N)
    (s : ↥(sliceLinks (N := N)) → Set G) :
    ∏ k : ↥(posLinks (N := N)), μG (rectExtend (G := G) hN s k)
      = ∏ ℓ : ↥(sliceLinks (N := N)), μG (s ℓ) := by
  have hinj : ∀ x ∈ (Finset.univ : Finset ↥(sliceLinks (N := N))),
      ∀ y ∈ (Finset.univ : Finset ↥(sliceLinks (N := N))),
      sliceIncl hN x = sliceIncl hN y → x = y :=
    fun x _ y _ h => sliceIncl_injective hN h
  have himage : ∏ k ∈ Finset.univ.image (sliceIncl hN),
        μG (rectExtend (G := G) hN s k)
      = ∏ ℓ : ↥(sliceLinks (N := N)), μG (s ℓ) := by
    rw [Finset.prod_image hinj]
    exact Finset.prod_congr rfl fun ℓ _ => by
      rw [rectExtend_sliceIncl]
  have hsub : ∏ k ∈ (Finset.univ.image (sliceIncl hN) :
        Finset ↥(posLinks (N := N))), μG (rectExtend (G := G) hN s k)
      = ∏ k : ↥(posLinks (N := N)), μG (rectExtend (G := G) hN s k) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro k _ hk
    rw [Finset.mem_image] at hk
    push_neg at hk
    rw [rectExtend_of_not_mem _ _ (fun ⟨ℓ, hℓ⟩ => hk ℓ (Finset.mem_univ ℓ) hℓ),
      measure_univ]
  rw [← hsub, himage]

/-- **The `posToSlice` marginal identity** (gap-theorem queue
Q1; named as an unproved loose end in `LatticeOSSpace` §7 and
in the transfer-matrix charter §2): the pushforward of the
product Haar measure on `posLinks` configurations under the
slice coordinatization is the product Haar measure on the
slice. -/
theorem posToSlice_map_measurePi (hN : Even N) :
    (Measure.pi fun _ : ↥(posLinks (N := N)) => μG).map
        (posToSlice (G := G) hN)
      = Measure.pi fun _ : ↥(sliceLinks (N := N)) => μG := by
  symm
  refine MeasureTheory.Measure.pi_eq ?_
  intro s hs
  rw [Measure.map_apply (continuous_posToSlice hN).measurable
        (MeasurableSet.pi (Set.countable_univ) (fun ℓ _ => hs ℓ)),
    posToSlice_preimage_pi, MeasureTheory.Measure.pi_pi,
    prod_rectExtend]

/-- The marginal identity in its `sliceMeasure` form: the
`posToSlice` pushforward of the product Haar measure on
`posLinks` is the slice measure at `β = 0`. -/
theorem posToSlice_map_sliceMeasure (hN : Even N) :
    (Measure.pi fun _ : ↥(posLinks (N := N)) => μG).map
        (posToSlice (G := G) hN)
      = sliceMeasure μG ρ 0 := by
  rw [posToSlice_map_measurePi, sliceMeasure_zero]

end ThetLogos
