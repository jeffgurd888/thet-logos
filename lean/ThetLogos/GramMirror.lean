/-
# Assembly, part 2: the mirror side (Route B, step T4b)

Companion brick to the Gram-clause campaign (Pitch 4, Stage 1b-B).
Charter: `whitepaper/gram-clause-scoping-2026-10-23.md`, §4 Route B,
step **T4** — split by the parent into **T4a** (landed:
`ThetLogos.GramAssembly` — instantiation + positive-half features),
**T4b** (this module: the mirror/B side scoped in GramAssembly's
§5), and **T4c** (series domination + the final discharge through
the integrated criterion). Steps T1 (the integrated criterion,
`ThetLogos.LatticeGramSeries`), T2 (the averaging projection,
`ThetLogos.AveragingProjection`) and T3 (the word/tensor
bookkeeping, `ThetLogos.GramWordTensor`) are landed.

## Content

* **Mirror stratum anatomy.** The negative half splits as
  `negLinks = mirrorStrictLinks ∪ negStratumLinks` (disjoint),
  the mirror of GramAssembly §1: `negStratumLinks` is the plane
  stratum seen from the negative half (time links based at
  `N - 1`), `mirrorStrictLinks` the non-plane part (the mirror
  image of `posLinks`). The split is a measure-preserving
  measurable equiv at `haarProb G` (`splitNegEquiv`).
* **The dual word.** A crossing-word datum `(slot, flag, a, b)`
  over the positive stratum has a mirrored dual datum over the
  negative stratum: slots transported by `stratumMirror` (the
  same-spatial-column identification of the two plane strata —
  the link reflection fixes both strata pointwise, so this column
  map is the transport between them) composed with `Fin.rev`
  order-reversal, flags transported under the same reversal,
  endpoints swapped. The **dual `γ` identity** (`dual_gamma`):
  the conjugated stratum integral of the dual word entry is the
  A-side coefficient `wordGamma`. This is what forces the *same*
  strict-half feature `Ξ` out of both marginals of the criterion.
* **Features.** The negative-half feature `featB` — the mirror
  scalar factor `φ₀ ∘ mirrorStrictMap` of the strict part times
  the conjugated dual word entry of the stratum part — with
  `featB_marginal` in the criterion's exact `hmargB` shape,
  per-word damping factor `dB = 1`, pairing with the *same*
  `featXi` as T4a, plus the `hBA`/`hBB`-shape companions.

## What remains for T4c

The concrete crossing features from the expansion of
`exp (-S₀)`, the Gram series identity `hgram`, the domination
`hsum`, and the final application of
`osForm_nonneg_of_gram_integrated`. This module does no series
domination and no discharge.

## Fences

Finite volume only; the corpus's unitary-valued `ρ` throughout;
`β` appears only as the criterion carries it — no sign condition
is used in this module. **NO CLAIM** — parts of any official
Clay statement closed by this module: 0.
-/

import ThetLogos.GramAssembly

open MeasureTheory
open scoped InnerProductSpace

namespace ThetLogos

namespace GramMirror

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [LocallyCompactSpace G]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §1. Mirror stratum anatomy (mirror of GramAssembly §1) -/

/-- The **strict negative half**: the non-plane part of the
negative half — the mirror image of `posLinks` under the link
reflection. -/
def mirrorStrictLinks : Finset (Link (Fin 4 → ZMod N)) :=
  negLinks \ planeLinks

/-- The **plane stratum inside the negative half**: the plane
links that lie in `negLinks` (the time links based at `N - 1`).
These are the free variables of the negative half once its
strict part is fixed — the mirror of `stratumLinks`. -/
def negStratumLinks : Finset (Link (Fin 4 → ZMod N)) :=
  negLinks ∩ planeLinks

theorem mem_negStratumLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ negStratumLinks (N := N) ↔ N / 2 ≤ (ℓ.1 0).val ∧ reflLink ℓ = ℓ := by
  simp only [negStratumLinks, Finset.mem_inter, mem_negLinks, mem_planeLinks]

theorem negStratumLinks_subset_negLinks :
    negStratumLinks (N := N) ⊆ negLinks := fun ℓ hℓ =>
  (Finset.mem_inter.mp hℓ).1

theorem mirrorStrictLinks_subset_negLinks :
    mirrorStrictLinks (N := N) ⊆ negLinks := fun ℓ hℓ =>
  (Finset.mem_sdiff.mp hℓ).1

/-- The negative half is the disjoint union of its strict part
and its stratum. -/
theorem mirrorStrict_union_negStratumLinks :
    mirrorStrictLinks (N := N) ∪ negStratumLinks = negLinks := by
  ext ℓ
  simp only [Finset.mem_union, mirrorStrictLinks, negStratumLinks,
    Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
  · intro h1
    by_cases h2 : ℓ ∈ planeLinks
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

theorem disjoint_mirrorStrict_negStratumLinks :
    Disjoint (mirrorStrictLinks (N := N)) (negStratumLinks) := by
  rw [Finset.disjoint_left]
  intro ℓ hℓ hℓ'
  exact (Finset.mem_sdiff.mp hℓ).2 (Finset.mem_inter.mp hℓ').2

/-- The index equiv between the negative half and the disjoint
union of its strict part and its stratum (a plain equiv, so its
components compute). -/
def negIndexEquiv :
    ↥(mirrorStrictLinks (N := N) ∪ negStratumLinks) ≃ ↥(negLinks (N := N)) :=
  ⟨fun x => ⟨x.1, by rw [← mirrorStrict_union_negStratumLinks]; exact x.2⟩,
   fun x => ⟨x.1, by rw [mirrorStrict_union_negStratumLinks]; exact x.2⟩,
   fun x => Subtype.ext rfl, fun x => Subtype.ext rfl⟩

/-- The strict part of a negative-half configuration. -/
def strictPartNeg (u : ↥(negLinks (N := N)) → G) :
    ↥(mirrorStrictLinks (N := N)) → G :=
  fun ℓ => u ⟨ℓ.1, mirrorStrictLinks_subset_negLinks ℓ.2⟩

/-- The stratum part of a negative-half configuration. -/
def negStratPart (u : ↥(negLinks (N := N)) → G) :
    ↥(negStratumLinks (N := N)) → G :=
  fun ℓ => u ⟨ℓ.1, negStratumLinks_subset_negLinks ℓ.2⟩

/-- **The negative-half split**: a negative-half configuration is
the pair of its strict-part restriction and its stratum part, as
a measurable equiv (the mirror of `splitHalfEquiv`). -/
noncomputable def splitNegEquiv :
    (↥(negLinks (N := N)) → G) ≃ᵐ
      ((↥(mirrorStrictLinks (N := N)) → G) × (↥(negStratumLinks (N := N)) → G)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↥(negLinks (N := N)) => G)
    negIndexEquiv).symm.trans
    (MeasurableEquiv.piFinsetUnion (fun _ : Link (Fin 4 → ZMod N) => G)
      disjoint_mirrorStrict_negStratumLinks).symm

theorem splitNegEquiv_fst (u : ↥(negLinks (N := N)) → G) :
    (splitNegEquiv u).1 = strictPartNeg u := by
  funext ℓ
  rfl

theorem splitNegEquiv_snd (u : ↥(negLinks (N := N)) → G) :
    (splitNegEquiv u).2 = negStratPart u := by
  funext ℓ
  rfl

/-- The negative-half split preserves the product Haar measure. -/
theorem measurePreserving_splitNegEquiv (μG : Measure G)
    [IsProbabilityMeasure μG] :
    MeasurePreserving (splitNegEquiv (N := N))
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      ((Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => μG)) :=
  (measurePreserving_piFinsetUnion disjoint_mirrorStrict_negStratumLinks
    (fun _ : Link (Fin 4 → ZMod N) => μG)).symm.comp
    (measurePreserving_piCongrLeft (fun _ : ↥(negLinks (N := N)) => μG)
      negIndexEquiv).symm

/-! ## §2. Words on the negative stratum (mirror of GramAssembly §2–§3) -/

/-- The **word entry** as a function of the negative-stratum
configuration: the `(a, b)` entry of the representation matrix of
the stratum word — the mirror of `GramAssembly.wordEntry`. -/
def wordEntryNeg {n : ℕ} (slot : Fin n → ↥(negStratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (u : ↥(negStratumLinks (N := N)) → G) : ℂ :=
  (repMatrix ρ (GramWordTensor.wordGroup
    (fun j => if flag j then u (slot j) else (u (slot j))⁻¹))) a b

/-- The **stratum integral of a negative-stratum word entry** —
the mirror of `wordGamma`, computed by `wordGammaNeg_eq` as T3's
finite path sum of averaging-operator coefficients. -/
noncomputable def wordGammaNeg {n : ℕ}
    (slot : Fin n → ↥(negStratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) : ℂ :=
  ∫ u, wordEntryNeg ρ slot flag a b u
    ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)

/-- **T3 headline 2 at the negative stratum**: the coefficient is
the finite path sum of T2-averaging coefficients at the path
endpoints. -/
theorem wordGammaNeg_eq {n : ℕ}
    (slot : Fin n → ↥(negStratumLinks (N := N))) (flag : Fin n → Bool)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (a b : Fin d) :
    wordGammaNeg ρ slot flag a b
    = ∑ p : Fin (n + 1) → Fin d,
        (if p 0 = a ∧ p (Fin.last n) = b then
          ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
              (GramWordTensor.pathA flag p),
            AveragingProjection.averagingOperator
              (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
              (GramWordTensor.occRepCLM slot
                (fun j => GramWordTensor.flavRep ρ (flag j)))
              (GramWordTensor.occRepCLM_continuous slot _
                (fun j => GramWordTensor.flavRep_continuous ρ flag
                  hρcont j))
              (GramWordTensor.occRepCLM_unitary slot _)
              ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathB flag p))⟫_ℂ
        else 0) :=
  GramWordTensor.integral_word_entry (μG := haarProb G) (ρ := ρ)
    slot flag hρcont a b

/-- The negative-stratum word entry is continuous in the stratum
configuration. -/
theorem wordEntryNeg_continuous {n : ℕ}
    (slot : Fin n → ↥(negStratumLinks (N := N))) (flag : Fin n → Bool)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (a b : Fin d) :
    Continuous (wordEntryNeg ρ slot flag a b) := by
  have hentry : Continuous fun M : Matrix (Fin d) (Fin d) ℂ => M a b :=
    (continuous_apply b).comp (continuous_apply a)
  exact hentry.comp (hρcont.comp (GramAssembly.continuous_wordGroup slot flag))

/-- The negative-stratum word entry is bounded by `1`
(unitarity). -/
theorem wordEntryNeg_norm_le_one {n : ℕ}
    (slot : Fin n → ↥(negStratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) (u : ↥(negStratumLinks (N := N)) → G) :
    ‖wordEntryNeg ρ slot flag a b u‖ ≤ 1 :=
  GramAssembly.repMatrix_entry_norm_le_one ρ _ a b

/-! ## §3. The stratum mirror and the dual word datum -/

/-- The positive plane stratum, characterized (even extent): the
time links based at `N / 2 - 1`. -/
theorem mem_stratumLinks_iff (hN : Even N) {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ GramAssembly.stratumLinks (N := N) ↔
      ℓ.2 = 0 ∧ (ℓ.1 0).val = N / 2 - 1 := by
  obtain ⟨m, hm⟩ := hN
  have hN0 : N ≠ 0 := NeZero.ne N
  rw [GramAssembly.mem_stratumLinks]
  constructor
  · rintro ⟨hlt, hfix⟩
    have hfix' : reflLink (ℓ.1, ℓ.2) = (ℓ.1, ℓ.2) := hfix
    obtain ⟨hdir, hval | hval⟩ :=
      (reflLink_eq_self_iff ⟨m, hm⟩ ℓ.1 ℓ.2).mp hfix'
    · exact ⟨hdir, hval⟩
    · omega
  · rintro ⟨hdir, hval⟩
    refine ⟨by omega, ?_⟩
    have hfix' : reflLink (ℓ.1, ℓ.2) = (ℓ.1, ℓ.2) :=
      (reflLink_eq_self_iff ⟨m, hm⟩ ℓ.1 ℓ.2).mpr ⟨hdir, Or.inl hval⟩
    exact hfix'

/-- The negative plane stratum, characterized (even extent): the
time links based at `N - 1`. -/
theorem mem_negStratumLinks_iff (hN : Even N) {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ negStratumLinks (N := N) ↔
      ℓ.2 = 0 ∧ (ℓ.1 0).val = N - 1 := by
  obtain ⟨m, hm⟩ := hN
  have hN0 : N ≠ 0 := NeZero.ne N
  rw [mem_negStratumLinks]
  constructor
  · rintro ⟨hle, hfix⟩
    have hfix' : reflLink (ℓ.1, ℓ.2) = (ℓ.1, ℓ.2) := hfix
    obtain ⟨hdir, hval | hval⟩ :=
      (reflLink_eq_self_iff ⟨m, hm⟩ ℓ.1 ℓ.2).mp hfix'
    · omega
    · exact ⟨hdir, hval⟩
  · rintro ⟨hdir, hval⟩
    refine ⟨by omega, ?_⟩
    have hfix' : reflLink (ℓ.1, ℓ.2) = (ℓ.1, ℓ.2) :=
      (reflLink_eq_self_iff ⟨m, hm⟩ ℓ.1 ℓ.2).mpr ⟨hdir, Or.inr hval⟩
    exact hfix'

theorem mem_negStratumLinks_of_update (hN : Even N)
    {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ GramAssembly.stratumLinks (N := N)) :
    (Function.update ℓ.1 0 ((N - 1 : ℕ) : ZMod N), ℓ.2)
      ∈ negStratumLinks (N := N) := by
  obtain ⟨m, hm⟩ := hN
  have hN0 : N ≠ 0 := NeZero.ne N
  rw [mem_negStratumLinks_iff ⟨m, hm⟩]
  obtain ⟨hdir, hval⟩ := (mem_stratumLinks_iff ⟨m, hm⟩).mp hℓ
  refine ⟨hdir, ?_⟩
  show (Function.update ℓ.1 0 ((N - 1 : ℕ) : ZMod N) 0).val = N - 1
  rw [Function.update_self, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

theorem mem_stratumLinks_of_update (hN : Even N)
    {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ negStratumLinks (N := N)) :
    (Function.update ℓ.1 0 ((N / 2 - 1 : ℕ) : ZMod N), ℓ.2)
      ∈ GramAssembly.stratumLinks (N := N) := by
  obtain ⟨m, hm⟩ := hN
  have hN0 : N ≠ 0 := NeZero.ne N
  rw [mem_stratumLinks_iff ⟨m, hm⟩]
  obtain ⟨hdir, hval⟩ := (mem_negStratumLinks_iff ⟨m, hm⟩).mp hℓ
  refine ⟨hdir, ?_⟩
  show (Function.update ℓ.1 0 ((N / 2 - 1 : ℕ) : ZMod N) 0).val = N / 2 - 1
  rw [Function.update_self, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- Moving a stratum site's time coordinate to the opposite plane
layer and back is the identity (the two layer values are the
sites' own time values, by the characterizations). -/
theorem update_update_stratumSite (hN : Even N)
    {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ GramAssembly.stratumLinks (N := N)) :
    Function.update (Function.update ℓ.1 0 ((N - 1 : ℕ) : ZMod N))
        0 ((N / 2 - 1 : ℕ) : ZMod N) = ℓ.1 := by
  obtain ⟨hdir, hval⟩ := (mem_stratumLinks_iff hN).mp hℓ
  have hx0 : ℓ.1 0 = ((N / 2 - 1 : ℕ) : ZMod N) :=
    ZMod.val_injective N (by
      rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt (by
        have hN0 : N ≠ 0 := NeZero.ne N
        obtain ⟨m, hm⟩ := hN
        omega)])
  rw [Function.update_idem, ← hx0]
  exact Function.update_eq_self 0 ℓ.1

/-- The mirror computation, from the negative side. -/
theorem update_update_negStratumSite (hN : Even N)
    {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ negStratumLinks (N := N)) :
    Function.update (Function.update ℓ.1 0 ((N / 2 - 1 : ℕ) : ZMod N))
        0 ((N - 1 : ℕ) : ZMod N) = ℓ.1 := by
  obtain ⟨hdir, hval⟩ := (mem_negStratumLinks_iff hN).mp hℓ
  have hx0 : ℓ.1 0 = ((N - 1 : ℕ) : ZMod N) :=
    ZMod.val_injective N (by
      rw [hval, ZMod.val_natCast, Nat.mod_eq_of_lt (by
        have hN0 : N ≠ 0 := NeZero.ne N
        obtain ⟨m, hm⟩ := hN
        omega)])
  rw [Function.update_idem, ← hx0]
  exact Function.update_eq_self 0 ℓ.1

/-- **The stratum mirror**: the identification of the positive
plane stratum with the negative one — same spatial column, time
coordinate moved to the mirror layer. The link reflection fixes
both strata pointwise (`reflLink_eq_self_iff`: both are layers
of time links), so this column map is the transport of slots
between the two strata. -/
def stratumMirror (hN : Even N) :
    ↥(GramAssembly.stratumLinks (N := N)) ≃ ↥(negStratumLinks (N := N)) where
  toFun ℓ := ⟨(Function.update ℓ.1.1 0 ((N - 1 : ℕ) : ZMod N), ℓ.1.2),
    mem_negStratumLinks_of_update hN ℓ.2⟩
  invFun ℓ := ⟨(Function.update ℓ.1.1 0 ((N / 2 - 1 : ℕ) : ZMod N), ℓ.1.2),
    mem_stratumLinks_of_update hN ℓ.2⟩
  left_inv ℓ := Subtype.ext (Prod.ext
    (update_update_stratumSite hN ℓ.2) rfl)
  right_inv ℓ := Subtype.ext (Prod.ext
    (update_update_negStratumSite hN ℓ.2) rfl)

/-- **The dual slot map**: the slots of the mirrored word — the
original slots read in `Fin.rev`-reversed order and transported
across the stratum mirror. -/
def dualSlot (hN : Even N) {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N))) :
    Fin n → ↥(negStratumLinks (N := N)) :=
  fun j => stratumMirror hN (slot (Fin.rev j))

/-- **The dual flag family**: the original flags read in
`Fin.rev`-reversed order — the flags flipped around by the
order-reversal. (With this choice the dual occurrence
representation, read backwards, is the original one:
`flavRep ρ (dualFlag flag j) = flavRep ρ (flag (Fin.rev j))`.) -/
def dualFlag {n : ℕ} (flag : Fin n → Bool) : Fin n → Bool :=
  fun j => flag (Fin.rev j)

/-! ## §4. The dual-word γ identity -/

/-- The path-reversal equiv on paths: an involution. -/
def pathRevEquiv {n : ℕ} : (Fin (n + 1) → Fin d) ≃ (Fin (n + 1) → Fin d) where
  toFun p := p ∘ Fin.rev
  invFun p := p ∘ Fin.rev
  left_inv p := by
    funext i
    simp [Function.comp_apply, Fin.rev_rev]
  right_inv p := by
    funext i
    simp [Function.comp_apply, Fin.rev_rev]

theorem rev_zero_last {n : ℕ} : Fin.rev (0 : Fin (n + 1)) = Fin.last n := by
  exact Fin.ext rfl

/-- **Coefficient transport across the stratum mirror.** The
`(X, Y)` occurrence coefficient of the dual word, integrated over
the negative stratum, is the `(X ∘ rev, Y ∘ rev)` coefficient of
the original word over the positive stratum: transport the
configurations by `piCongrLeft` of `stratumMirror`, then reindex
the occurrence product by `Fin.rev`; the dual flavors read
backwards are the original flavors. -/
theorem integral_occMat_dual {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N))) (flag : Fin n → Bool)
    (hN : Even N) (X Y : Fin n → Fin d) :
    ∫ u, GramWordTensor.occMat (dualSlot hN slot)
          (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)) u X Y
        ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
      = ∫ s, GramWordTensor.occMat slot
          (fun j => GramWordTensor.flavRep ρ (flag j)) s
          (X ∘ Fin.rev) (Y ∘ Fin.rev)
        ∂(Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N)) => haarProb G) := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(negStratumLinks (N := N)) => G)
        (stratumMirror hN))
      (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N)) => haarProb G)
      (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G) :=
    measurePreserving_piCongrLeft
      (fun _ : ↥(negStratumLinks (N := N)) => haarProb G) (stratumMirror hN)
  rw [← hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
    (fun u => GramWordTensor.occMat (dualSlot hN slot)
      (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)) u X Y)]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only
  rw [GramWordTensor.occMat_apply, GramWordTensor.occMat_apply]
  have hpt : ∀ j : Fin n,
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(negStratumLinks (N := N)) => G)
        (stratumMirror hN)) s (dualSlot hN slot j) = s (slot (Fin.rev j)) :=
    fun j => MeasurableEquiv.piCongrLeft_apply_apply _ _ _
  calc ∏ j, repMatrix (GramWordTensor.flavRep ρ (dualFlag flag j))
          ((MeasurableEquiv.piCongrLeft
            (fun _ : ↥(negStratumLinks (N := N)) => G)
            (stratumMirror hN)) s (dualSlot hN slot j)) (X j) (Y j)
      = ∏ j, repMatrix (GramWordTensor.flavRep ρ (flag (Fin.rev j)))
          (s (slot (Fin.rev j))) (X j) (Y j) :=
        Finset.prod_congr rfl fun j _ => by simp only [hpt j, dualFlag]
    _ = ∏ k, repMatrix (GramWordTensor.flavRep ρ (flag k)) (s (slot k))
          (X (Fin.rev k)) (Y (Fin.rev k)) := by
        rw [← Equiv.prod_comp Fin.revPerm
          (fun k => repMatrix (GramWordTensor.flavRep ρ (flag k)) (s (slot k))
            (X (Fin.rev k)) (Y (Fin.rev k)))]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [Fin.revPerm_apply, Fin.rev_rev]
    _ = ∏ k, repMatrix (GramWordTensor.flavRep ρ (flag k)) (s (slot k))
          ((X ∘ Fin.rev) k) ((Y ∘ Fin.rev) k) :=
        Finset.prod_congr rfl fun k _ => rfl

/-- **Coefficient transport, operator form.** The dual averaging
operator's `(X, Y)` coefficient is the original averaging
operator's `(X ∘ rev, Y ∘ rev)` coefficient. -/
theorem coeff_dual {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N))) (flag : Fin n → Bool)
    (hN : Even N) (hρcont : Continuous fun g : G => repMatrix ρ g)
    (X Y : Fin n → Fin d) :
    ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ) X,
      AveragingProjection.averagingOperator
        (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
        (GramWordTensor.occRepCLM (dualSlot hN slot)
          (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
        (GramWordTensor.occRepCLM_continuous _ _
          (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag) hρcont j))
        (GramWordTensor.occRepCLM_unitary _ _)
        ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ) Y)⟫_ℂ
    = ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ) (X ∘ Fin.rev),
        AveragingProjection.averagingOperator
          (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N)) => haarProb G)
          (GramWordTensor.occRepCLM slot
            (fun j => GramWordTensor.flavRep ρ (flag j)))
          (GramWordTensor.occRepCLM_continuous _ _
            (fun j => GramWordTensor.flavRep_continuous ρ flag hρcont j))
          (GramWordTensor.occRepCLM_unitary _ _)
          ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ) (Y ∘ Fin.rev))⟫_ℂ :=
  (GramWordTensor.integral_occMat_eq_averaging (μG := haarProb G)
    (dualSlot hN slot) (fun j => GramWordTensor.flavRep ρ (dualFlag flag j))
    (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag) hρcont j)
    X Y).symm.trans
  ((integral_occMat_dual ρ slot flag hN X Y).trans
    (GramWordTensor.integral_occMat_eq_averaging (μG := haarProb G)
      slot (fun j => GramWordTensor.flavRep ρ (flag j))
      (fun j => GramWordTensor.flavRep_continuous ρ flag hρcont j)
      (X ∘ Fin.rev) (Y ∘ Fin.rev)))

/-- The dual path data, read backwards, is the original path
data with the two endpoint roles swapped: the `B`-indices of
the dual word are the `A`-indices of the original. -/
theorem pathB_dual_comp_rev {n : ℕ} (flag : Fin n → Bool)
    (p : Fin (n + 1) → Fin d) :
    GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev) ∘ Fin.rev
      = GramWordTensor.pathA flag p := by
  funext j
  simp only [Function.comp_apply]
  unfold GramWordTensor.pathB GramWordTensor.pathA dualFlag
  simp only [Function.comp_apply, Fin.rev_rev, Fin.rev_succ, Fin.rev_castSucc]

/-- The companion swap for the `A`-indices. -/
theorem pathA_dual_comp_rev {n : ℕ} (flag : Fin n → Bool)
    (p : Fin (n + 1) → Fin d) :
    GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev) ∘ Fin.rev
      = GramWordTensor.pathB flag p := by
  funext j
  simp only [Function.comp_apply]
  unfold GramWordTensor.pathA GramWordTensor.pathB dualFlag
  simp only [Function.comp_apply, Fin.rev_rev, Fin.rev_succ, Fin.rev_castSucc]

/-- **The dual-word `γ` identity (the content of T4b).** For a
crossing-word datum `(slot, flag, a, b)` and its mirrored dual
datum (slots transported by `stratumMirror` under `Fin.rev`
reversal, flags transported under the same reversal, endpoints
swapped), the conjugated stratum integral of the dual word entry
is the A-side coefficient `wordGamma`. Proof: `integral_conj`,
T3's path-sum form on both sides, conjugation and
self-adjointness of the dual averaging operator (T2), the
coefficient transport across the stratum mirror, and the path
reindexing by `Fin.rev` — termwise, the dual path data read
backwards is the original path data with endpoints swapped. -/
theorem dual_gamma {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N))) (flag : Fin n → Bool)
    (hN : Even N) (hρcont : Continuous fun g : G => repMatrix ρ g) (a b : Fin d) :
    ∫ u, (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a u)
        ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
      = GramAssembly.wordGamma ρ slot flag a b := by
  classical
  have hterm : ∀ p : Fin (n + 1) → Fin d,
      (starRingEnd ℂ) (if (p ∘ Fin.rev) 0 = b ∧ (p ∘ Fin.rev) (Fin.last n) = a then
          ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
              (GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev)),
            AveragingProjection.averagingOperator
              (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
              (GramWordTensor.occRepCLM (dualSlot hN slot)
                (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
              (GramWordTensor.occRepCLM_continuous _ _
                (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                  hρcont j))
              (GramWordTensor.occRepCLM_unitary _ _)
              ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev)))⟫_ℂ
        else 0)
      = (if p 0 = a ∧ p (Fin.last n) = b then
          ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
              (GramWordTensor.pathA flag p),
            AveragingProjection.averagingOperator
              (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N)) => haarProb G)
              (GramWordTensor.occRepCLM slot
                (fun j => GramWordTensor.flavRep ρ (flag j)))
              (GramWordTensor.occRepCLM_continuous _ _
                (fun j => GramWordTensor.flavRep_continuous ρ flag hρcont j))
              (GramWordTensor.occRepCLM_unitary _ _)
              ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathB flag p))⟫_ℂ
        else 0) := by
    intro p
    have hcond : ((p ∘ Fin.rev) 0 = b ∧ (p ∘ Fin.rev) (Fin.last n) = a)
        ↔ (p 0 = a ∧ p (Fin.last n) = b) := by
      have e1 : (p ∘ Fin.rev) 0 = p (Fin.last n) := by
        simp only [Function.comp_apply, rev_zero_last]
      have e2 : (p ∘ Fin.rev) (Fin.last n) = p 0 := by
        simp only [Function.comp_apply, Fin.rev_last]
      rw [e1, e2]
      exact and_comm
    by_cases h : p 0 = a ∧ p (Fin.last n) = b
    · rw [if_pos (hcond.mpr h), if_pos h]
      calc (starRingEnd ℂ)
            ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev)),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
                (GramWordTensor.occRepCLM (dualSlot hN slot)
                  (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                    hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev)))⟫_ℂ
          = ⟪AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
                (GramWordTensor.occRepCLM (dualSlot hN slot)
                  (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                    hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev))),
              (EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev))⟫_ℂ :=
            inner_conj_symm _ _
        _ = ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev)),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
                (GramWordTensor.occRepCLM (dualSlot hN slot)
                  (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                    hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev)))⟫_ℂ :=
            AveragingProjection.self_adjoint_inner _ _
              (GramWordTensor.occRepCLM_continuous _ _
                (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                  hρcont j))
              (fun s t v => by
                rw [GramWordTensor.occRepCLM_mul,
                  ContinuousLinearMap.mul_apply])
              (fun v => by
                rw [GramWordTensor.occRepCLM_one,
                  ContinuousLinearMap.one_apply])
              (GramWordTensor.occRepCLM_unitary _ _) _ _
        _ = ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathA flag p),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N))
                  => haarProb G)
                (GramWordTensor.occRepCLM slot
                  (fun j => GramWordTensor.flavRep ρ (flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ flag hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathB flag p))⟫_ℂ := by
            rw [coeff_dual ρ slot flag hN hρcont
              (GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev))
              (GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev)),
              pathB_dual_comp_rev, pathA_dual_comp_rev]
    · rw [if_neg (fun h' => h (hcond.mp h')), if_neg h]
      exact map_zero _
  calc ∫ u, (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a u)
          ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
      = (starRingEnd ℂ) (wordGammaNeg ρ (dualSlot hN slot) (dualFlag flag) b a) := by
        show ∫ u, (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a u)
            ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
          = (starRingEnd ℂ) (∫ u, wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a u
            ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G))
        rw [← integral_conj]
    _ = ∑ p : Fin (n + 1) → Fin d, (starRingEnd ℂ)
          (if p 0 = b ∧ p (Fin.last n) = a then
            ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathA (dualFlag flag) p),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
                (GramWordTensor.occRepCLM (dualSlot hN slot)
                  (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                    hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathB (dualFlag flag) p))⟫_ℂ
          else 0) := by
        rw [wordGammaNeg_eq ρ (dualSlot hN slot) (dualFlag flag) hρcont b a, map_sum]
    _ = ∑ p : Fin (n + 1) → Fin d, (starRingEnd ℂ)
          (if (p ∘ Fin.rev) 0 = b ∧ (p ∘ Fin.rev) (Fin.last n) = a then
            ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathA (dualFlag flag) (p ∘ Fin.rev)),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)
                (GramWordTensor.occRepCLM (dualSlot hN slot)
                  (fun j => GramWordTensor.flavRep ρ (dualFlag flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ (dualFlag flag)
                    hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathB (dualFlag flag) (p ∘ Fin.rev)))⟫_ℂ
          else 0) :=
        (Equiv.sum_comp pathRevEquiv _).symm
    _ = ∑ p : Fin (n + 1) → Fin d,
          (if p 0 = a ∧ p (Fin.last n) = b then
            ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathA flag p),
              AveragingProjection.averagingOperator
                (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N))
                  => haarProb G)
                (GramWordTensor.occRepCLM slot
                  (fun j => GramWordTensor.flavRep ρ (flag j)))
                (GramWordTensor.occRepCLM_continuous _ _
                  (fun j => GramWordTensor.flavRep_continuous ρ flag hρcont j))
                (GramWordTensor.occRepCLM_unitary _ _)
                ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                  (GramWordTensor.pathB flag p))⟫_ℂ
          else 0) :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = GramAssembly.wordGamma ρ slot flag a b := by
        rw [GramAssembly.wordGamma_eq ρ slot flag hρcont a b]

/-! ## §5. The strict mirror map and the B-side features -/

/-- The reflection equiv between the strict positive half and
the strict negative half (the link reflection, an involution). -/
def mirrorIndexEquiv (hN : Even N) :
    ↥(posLinks (N := N)) ≃ ↥(mirrorStrictLinks (N := N)) where
  toFun ℓ := ⟨reflLink ℓ.1, Finset.mem_sdiff.mpr
    ⟨reflLink_mem_negLinks hN ℓ.2, reflLink_not_mem_planeLinks ℓ.2⟩⟩
  invFun m := ⟨reflLink m.1, reflLink_mem_posLinks hN
    (Finset.mem_sdiff.mp m.2).1 (Finset.mem_sdiff.mp m.2).2⟩
  left_inv ℓ := Subtype.ext (reflLink_involutive ℓ.1)
  right_inv m := Subtype.ext (reflLink_involutive m.1)

/-- **The strict mirror map**: a strict-negative-half
configuration read on the strict positive half through the link
reflection, with inversion on time links — `mirrorP`'s formula,
restricted to the strict part. -/
def mirrorStrictMap (hN : Even N) (v : ↥(mirrorStrictLinks (N := N)) → G) :
    ↥(posLinks (N := N)) → G :=
  fun ℓ => if ℓ.1.2 = 0
    then (v (mirrorIndexEquiv hN ℓ))⁻¹
    else v (mirrorIndexEquiv hN ℓ)

/-- **The mirror factors through the strict part.** `mirrorP`
reads a negative-half configuration only at the reflections of
strict positive links — strict negative links — so it is the
strict mirror map of the strict part. (The two readings of each
link agree because subtype proofs are irrelevant.) -/
theorem mirrorP_eq_mirrorStrictMap (hN : Even N)
    (u : ↥(negLinks (N := N)) → G) :
    mirrorP hN u = mirrorStrictMap hN (strictPartNeg u) := by
  have hpt : ∀ ℓ : ↥(posLinks (N := N)),
      strictPartNeg u (mirrorIndexEquiv hN ℓ)
        = u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ :=
    fun ℓ => rfl
  funext ℓ
  by_cases h : ℓ.1.2 = 0
  · rw [show mirrorP hN u ℓ
        = (u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from if_pos h,
      show mirrorStrictMap hN (strictPartNeg u) ℓ
        = ((strictPartNeg u) (mirrorIndexEquiv hN ℓ))⁻¹ from if_pos h,
      hpt]
  · rw [show mirrorP hN u ℓ
        = u ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from if_neg h,
      show mirrorStrictMap hN (strictPartNeg u) ℓ
        = (strictPartNeg u) (mirrorIndexEquiv hN ℓ) from if_neg h,
      hpt]

/-- The strict mirror map is continuous (coordinatewise: a fixed
coordinate, possibly inverted). -/
theorem mirrorStrictMap_continuous (hN : Even N) :
    Continuous (mirrorStrictMap (G := G) (N := N) hN) := by
  refine continuous_pi fun ℓ => ?_
  show Continuous fun v : ↥(mirrorStrictLinks (N := N)) → G =>
    if ℓ.1.2 = 0 then (v (mirrorIndexEquiv hN ℓ))⁻¹
      else v (mirrorIndexEquiv hN ℓ)
  by_cases h : ℓ.1.2 = 0
  · rw [show (fun v : ↥(mirrorStrictLinks (N := N)) → G =>
        if ℓ.1.2 = 0 then (v (mirrorIndexEquiv hN ℓ))⁻¹
          else v (mirrorIndexEquiv hN ℓ))
      = fun v => (v (mirrorIndexEquiv hN ℓ))⁻¹ from
      funext fun v => if_pos h]
    exact Continuous.inv (continuous_apply (mirrorIndexEquiv hN ℓ))
  · rw [show (fun v : ↥(mirrorStrictLinks (N := N)) → G =>
        if ℓ.1.2 = 0 then (v (mirrorIndexEquiv hN ℓ))⁻¹
          else v (mirrorIndexEquiv hN ℓ))
      = fun v => v (mirrorIndexEquiv hN ℓ) from
      funext fun v => if_neg h]
    exact continuous_apply (mirrorIndexEquiv hN ℓ)

/-- Restriction to the strict part is continuous. -/
theorem continuous_strictPartNeg :
    Continuous fun u : ↥(negLinks (N := N)) → G => strictPartNeg u :=
  continuous_pi fun ℓ => continuous_apply _

/-- Restriction to the stratum part is continuous. -/
theorem continuous_negStratPart :
    Continuous fun u : ↥(negLinks (N := N)) → G => negStratPart u :=
  continuous_pi fun ℓ => continuous_apply _

/-- **The negative-half feature of one crossing-word datum**
(the criterion's `𝒝`-side feature shape): the mirror scalar
factor — the observable read through the strict mirror map of
the strict part — times the conjugated dual word entry of the
stratum part. The conjugation is the one the criterion's
`hgram` applies to the `B` family, and it is exactly what the
dual `γ` identity of §4 consumes. -/
def featB {n : ℕ} (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ) (hN : Even N)
    (u : ↥(negLinks (N := N)) → G) : ℂ :=
  φ₀ (mirrorStrictMap hN (strictPartNeg u))
    * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
        (negStratPart u))

/-- Features are continuous. -/
theorem featB_continuous {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Continuous (featB ρ slot flag a b φ₀ hN) := by
  have h1 : Continuous fun u : ↥(negLinks (N := N)) → G =>
      φ₀ (mirrorStrictMap hN (strictPartNeg u)) :=
    (hφ₀.comp (mirrorStrictMap_continuous hN)).comp continuous_strictPartNeg
  have h2 : Continuous fun u : ↥(negLinks (N := N)) → G =>
      (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag)
        b a (negStratPart u)) :=
    (continuous_star.comp (wordEntryNeg_continuous ρ (dualSlot hN slot)
      (dualFlag flag) hρcont b a)).comp continuous_negStratPart
  exact h1.mul h2

/-- Features are bounded by the observable's bound (the dual word
entry contributes a factor `≤ 1`, conjugation-invisible). -/
theorem featB_norm_le {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    {Cφ : ℝ} (hφ₀ : ∀ z, ‖φ₀ z‖ ≤ Cφ) (hN : Even N)
    (u : ↥(negLinks (N := N)) → G) :
    ‖featB ρ slot flag a b φ₀ hN u‖ ≤ Cφ := by
  have hnorm : ‖(starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot)
        (dualFlag flag) b a (negStratPart u))‖
      = ‖wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
          (negStratPart u)‖ := by
    simp
  have h1 : ‖featB ρ slot flag a b φ₀ hN u‖
      = ‖φ₀ (mirrorStrictMap hN (strictPartNeg u))‖
        * ‖wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
            (negStratPart u)‖ := by
    rw [featB, norm_mul, hnorm]
  rw [h1]
  have h2 := mul_le_mul (hφ₀ (mirrorStrictMap hN (strictPartNeg u)))
    (wordEntryNeg_norm_le_one ρ (dualSlot hN slot) (dualFlag flag) b a
      (negStratPart u))
    (norm_nonneg _)
    (le_trans (norm_nonneg _) (hφ₀ (mirrorStrictMap hN (strictPartNeg u))))
  simpa using h2

/-- Features are almost-everywhere strongly measurable against
the negative-half product measure (the criterion's `hBA`-side
shape, per feature). -/
theorem featB_aestronglyMeasurable {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    AEStronglyMeasurable (featB ρ slot flag a b φ₀ hN)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) :=
  (featB_continuous ρ slot flag a b φ₀ hφ₀ hN hρcont).aestronglyMeasurable

/-- Integrating a strict-part function over the negative half is
integrating it over the strict part (the stratum factor is a
probability measure and integrates out) — the unconditional,
junk-value form, through `integral_prod_mul`. -/
theorem integral_strictPartNeg (F : (↥(mirrorStrictLinks (N := N)) → G) → ℂ) :
    ∫ u, F (strictPartNeg u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ∫ v, F v
          ∂(Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G) := by
  have step1 : ∫ u, F (strictPartNeg u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ∫ p, F p.1
          ∂((Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G).prod
            (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)) := by
    rw [← (measurePreserving_splitNegEquiv (haarProb G)).integral_comp
      (MeasurableEquiv.measurableEmbedding _)
      (fun p : (↥(mirrorStrictLinks (N := N)) → G)
        × (↥(negStratumLinks (N := N)) → G) => F p.1)]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only
    rw [splitNegEquiv_fst]
  rw [step1]
  have step2 : ∫ p, F p.1
        ∂((Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G).prod
          (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G))
      = ∫ p, F p.1 * (1 : ℂ)
        ∂((Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G).prod
          (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    dsimp only
    rw [mul_one]
  rw [step2]
  have h3 : ∫ p, F p.1 * (1 : ℂ)
        ∂((Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G).prod
          (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G))
      = (∫ v, F v
          ∂(Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G))
        * ∫ w, (1 : ℂ)
          ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G) :=
    MeasureTheory.integral_prod_mul F (fun _ => (1 : ℂ))
  rw [h3, MeasureTheory.integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul, mul_one]

/-- **The B-side marginal (the criterion's `hmargB` shape, for
one word datum, per-word factor `dB = 1`)**: integrating the
feature against a positive-half observable composed with
`mirrorP` over the negative half leaves the *same* strict-half
feature `featXi` as T4a's A-side marginal, paired with the same
observable. The strict factor is transported by the corpus's
`integral_mirrorP` through the factoring of `mirrorP` over the
strict part; the stratum factor is the dual `γ` identity of §4
(the only step consuming `hρcont`). -/
theorem featB_marginal {n : ℕ}
    (slot : Fin n → ↥(GramAssembly.stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ) (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (f : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ u, featB ρ slot flag a b φ₀ hN u * f (mirrorP hN u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ((1 : ℝ) : ℂ) * ∫ z, GramAssembly.featXi ρ slot flag a b φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
  classical
  have hstrict : ∫ v, φ₀ (mirrorStrictMap hN v) * f (mirrorStrictMap hN v)
        ∂(Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G)
      = ∫ z, φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
    calc ∫ v, φ₀ (mirrorStrictMap hN v) * f (mirrorStrictMap hN v)
            ∂(Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G)
        = ∫ u, φ₀ (mirrorStrictMap hN (strictPartNeg u))
              * f (mirrorStrictMap hN (strictPartNeg u))
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) :=
          (integral_strictPartNeg (fun v => φ₀ (mirrorStrictMap hN v)
            * f (mirrorStrictMap hN v))).symm
      _ = ∫ u, (φ₀ * f) (mirrorP hN u)
            ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          dsimp only
          rw [mirrorP_eq_mirrorStrictMap]
          rfl
      _ = ∫ z, (φ₀ * f) z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) :=
          integral_mirrorP (haarProb G) hN _
      _ = ∫ z, φ₀ z * f z
            ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          dsimp only
          rfl
  have hcomp : ∫ u, featB ρ slot flag a b φ₀ hN u * f (mirrorP hN u)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ∫ u, (φ₀ (mirrorStrictMap hN (splitNegEquiv u).1)
            * f (mirrorStrictMap hN (splitNegEquiv u).1))
          * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
            (splitNegEquiv u).2)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) := by
    congr 1
    funext u
    show φ₀ (mirrorStrictMap hN (strictPartNeg u))
        * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
            (negStratPart u)) * f (mirrorP hN u)
      = (φ₀ (mirrorStrictMap hN (splitNegEquiv u).1)
          * f (mirrorStrictMap hN (splitNegEquiv u).1))
        * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
            (splitNegEquiv u).2)
    rw [mirrorP_eq_mirrorStrictMap, ← splitNegEquiv_fst, ← splitNegEquiv_snd]
    ring
  calc ∫ u, featB ρ slot flag a b φ₀ hN u * f (mirrorP hN u)
          ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G)
      = ∫ u, (φ₀ (mirrorStrictMap hN (splitNegEquiv u).1)
            * f (mirrorStrictMap hN (splitNegEquiv u).1))
          * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
            (splitNegEquiv u).2)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => haarProb G) := hcomp
    _ = ∫ p, (φ₀ (mirrorStrictMap hN p.1) * f (mirrorStrictMap hN p.1))
          * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag) b a
            p.2)
          ∂((Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G).prod
            (Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G)) := by
        rw [← (measurePreserving_splitNegEquiv (haarProb G)).integral_comp
          (MeasurableEquiv.measurableEmbedding _)
          (fun p : (↥(mirrorStrictLinks (N := N)) → G)
            × (↥(negStratumLinks (N := N)) → G) =>
            (φ₀ (mirrorStrictMap hN p.1) * f (mirrorStrictMap hN p.1))
            * (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag)
              b a p.2))]
    _ = (∫ v, φ₀ (mirrorStrictMap hN v) * f (mirrorStrictMap hN v)
          ∂(Measure.pi fun _ : ↥(mirrorStrictLinks (N := N)) => haarProb G))
        * ∫ w, (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot) (dualFlag flag)
            b a w)
          ∂(Measure.pi fun _ : ↥(negStratumLinks (N := N)) => haarProb G) :=
        MeasureTheory.integral_prod_mul
          (fun v => φ₀ (mirrorStrictMap hN v) * f (mirrorStrictMap hN v))
          (fun w => (starRingEnd ℂ) (wordEntryNeg ρ (dualSlot hN slot)
            (dualFlag flag) b a w))
    _ = (∫ z, φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
        * GramAssembly.wordGamma ρ slot flag a b := by
        rw [hstrict, dual_gamma ρ slot flag hN hρcont a b]
    _ = ((1 : ℝ) : ℂ) * ∫ z, GramAssembly.featXi ρ slot flag a b φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
        have e : (∫ z, GramAssembly.featXi ρ slot flag a b φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
            = GramAssembly.wordGamma ρ slot flag a b * ∫ z, φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
          rw [show (fun z => GramAssembly.featXi ρ slot flag a b φ₀ z * f z)
              = fun z => GramAssembly.wordGamma ρ slot flag a b * (φ₀ z * f z) from
            funext fun z => by simp only [GramAssembly.featXi]; ring]
          exact MeasureTheory.integral_const_mul _ _
        rw [e, Complex.ofReal_one, one_mul, mul_comm]

end GramMirror

end ThetLogos
