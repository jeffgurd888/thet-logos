import ThetLogos.QuadReMomentTelescope
import ThetLogos.RepTensorTwirl
import ThetLogos.PrimitiveQuadPatterns

/-
# PW-5a: the interface brick of the `Φ` assembly

This module is the first of three sub-bricks (PW-5a/b/c) that
assemble the sign of `Φ` on the diagonal. It is extended by
append in place: §5a.1 (the `e1` pack), §5a.2 (the `C4` cycle
ordering), §5a.3 (the split-list check). Later sub-bricks
append their own sections to this same file.

**Fences.** NO CLAIM; dials 0/4. Parts of the Clay
Yang–Mills statement closed by this module: **0**. This
brick is an *interface*: it evaluates nothing and asserts
no sign. It fixes the baseline facts the assembly consumes
(the mean character `e1` vanishes at irreducible `ρ`,
including the dimension-`1` split), the cyclic ordering of
a primitive quad's columns and sites at the assembly's `N`,
and the list of orientation splits a `C4` quad can carry,
checked against the geometry (pre-registered K-PW-5-1).
Finite-volume algebra and finite combinatorics only; no
limit is taken or asserted; `N = 2` is not touched.

Namespace/vocabulary notes (corrections to the brief's
expectations, recorded on the face): the corpus's `e1` is
defined in `PlaneCrossingBeta2` (not Beta4):
`e1 ρ μG = ∫ g, (charFn ρ g).re ∂μG`. The dimension-`1`
nontriviality hypothesis is stated in owned vocabulary as
`∃ h : G, charFn ρ h ≠ 1` — the character is not the
constant `1` function, read at one group element.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix

/-! ## §5a.1. The `e1` pack

At irreducible `ρ` the baseline `e1⁴` of `phiFunctional`
vanishes in every dimension: at `2 ≤ d` by PW-1's
`integral_charFn_eq_zero`; at `d = 1` the character is a
one-dimensional character of `G`, either trivial — then
`e1 = 1` and every diagonal summand of `Φ` is `1 - 1` — or
nontrivial, when the Haar-invariance argument below gives
`∫ χ = 0` directly. At `d = 0` everything is vacuous.
-/

section E1Pack

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **The baseline vanishes at irreducible `ρ`, `2 ≤ d`.**
`e1 ρ μG = (∫ g, χ(g) ∂μG).re` (real part of the integral
of the character, by `integral_re`), and PW-1's
`integral_charFn_eq_zero` evaluates the character integral
itself to `0`. -/
theorem e1_eq_zero_of_irreducible (hρirr : RepIrreducible ρ) (hd : 2 ≤ d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) : e1 ρ μG = 0 := by
  have h := integral_charFn_eq_zero μG ρ hρirr hd hρcont
  have hre : (∫ g, (charFn ρ g).re ∂μG) = (∫ g, charFn ρ g ∂μG).re :=
    integral_re (integrable_charFn ρ μG hρcont)
  show (∫ g, (charFn ρ g).re ∂μG) = 0
  rw [hre, h]
  simp

/-- At `d = 1` the character is the single diagonal entry:
the trace over `Fin 1` collapses to the `(0, 0)` entry. -/
theorem charFn_eq_entry_of_dim_one (hd : d = 1) (g : G) :
    charFn ρ g = repMatrix ρ g ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  subst hd
  show Matrix.trace (repMatrix ρ g) = repMatrix ρ g ⟨0, by omega⟩ ⟨0, by omega⟩
  rw [Matrix.trace, Fin.sum_univ_one]
  rfl

/-- At `d = 1` the character is multiplicative: a
one-dimensional unitary representation is a character of
the group in the elementary sense. -/
theorem charFn_mul_of_dim_one (hd : d = 1) (a b : G) :
    charFn ρ (a * b) = charFn ρ a * charFn ρ b := by
  subst hd
  rw [charFn_eq_entry_of_dim_one ρ rfl, charFn_eq_entry_of_dim_one ρ rfl,
    charFn_eq_entry_of_dim_one ρ rfl, repMatrix_mul, Matrix.mul_apply,
    Fin.sum_univ_one]
  rfl

/-- **The dimension-`1` vanishing, nontrivial case.** If
some `h : G` has `χ(h) ≠ 1`, then left-invariance of the
Haar integral gives `χ(h) • ∫ χ = ∫ χ` (the integrand at
`h * g` is `χ(h) * χ(g)` by one-dimensional
multiplicativity), so `(χ(h) - 1) • ∫ χ = 0` and the
integral is `0`. -/
theorem integral_charFn_eq_zero_of_dim_one_ne (hd : d = 1)
    (hne : ∃ h : G, charFn ρ h ≠ 1) :
    ∫ g, charFn ρ g ∂μG = 0 := by
  obtain ⟨h, hh⟩ := hne
  have key : charFn ρ h * (∫ g, charFn ρ g ∂μG) = ∫ g, charFn ρ g ∂μG := by
    have h1 : charFn ρ h * (∫ g, charFn ρ g ∂μG)
        = ∫ g, charFn ρ (h * g) ∂μG := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show charFn ρ h * charFn ρ g = charFn ρ (h * g)
      rw [charFn_mul_of_dim_one ρ hd]
    rw [h1, integral_mul_left_eq_self]
  have h2 : (charFn ρ h - 1) * (∫ g, charFn ρ g ∂μG) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hh
  · exact h3

/-- At `d = 1` with `ρ` nontrivial, `e1` vanishes: the
character integral itself is `0` by the invariance
argument, and `e1` is its real part. -/
theorem e1_eq_zero_of_dim_one_ne (hd : d = 1)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hne : ∃ h : G, charFn ρ h ≠ 1) : e1 ρ μG = 0 := by
  have h := integral_charFn_eq_zero_of_dim_one_ne ρ μG hd hne
  have hre : (∫ g, (charFn ρ g).re ∂μG) = (∫ g, charFn ρ g ∂μG).re :=
    integral_re (integrable_charFn ρ μG hρcont)
  show (∫ g, (charFn ρ g).re ∂μG) = 0
  rw [hre, h]
  simp

/-- At `d = 1` with `ρ` trivial, the character is
identically `1`: the trace of the identity matrix over
`Fin 1`. -/
theorem charFn_eq_one_of_dim_one_trivial (hd : d = 1)
    (htriv : ∀ g, repMatrix ρ g = 1) (g : G) : charFn ρ g = 1 := by
  subst hd
  show Matrix.trace (repMatrix ρ g) = 1
  rw [htriv g]
  simp

/-- At `d = 1` with `ρ` trivial, `e1 = 1`: the integrand
is constantly `(1 : ℂ).re = 1` and `μG` is a probability
measure. -/
theorem e1_eq_one_of_dim_one_trivial (hd : d = 1)
    (htriv : ∀ g, repMatrix ρ g = 1) : e1 ρ μG = 1 := by
  show (∫ g, (charFn ρ g).re ∂μG) = 1
  have h1 : (fun g : G => (charFn ρ g).re) = fun _ => (1 : ℝ) := by
    funext g
    rw [charFn_eq_one_of_dim_one_trivial ρ hd htriv g]
    simp
  rw [h1]
  simp [Measure.real]

/-- At `d = 1` with `ρ` trivial, every diagonal
`quadReMoment` is `1`: every column factor `colRe` is
`(1 : ℂ).re = 1`, so the integrand is constantly `1`
over the product probability measure. -/
theorem quadReMoment_eq_one_of_dim_one_trivial (hd : d = 1)
    (htriv : ∀ g, repMatrix ρ g = 1) (C : Finset (LayerColumn N))
    (u : LayerLink N → G) : quadReMoment ρ μG C u u = 1 := by
  have hcol : ∀ (P : LayerColumn N) (α : LayerSite N → G),
      colRe ρ u u P α = 1 := by
    intro P α
    show (charFn ρ _).re = 1
    rw [charFn_eq_one_of_dim_one_trivial ρ hd htriv]
    simp
  have h1 : (fun α : LayerSite N → G => ∏ P ∈ C, colRe ρ u u P α)
      = fun _ => (1 : ℝ) := by
    funext α
    exact Finset.prod_eq_one (fun P _ => hcol P α)
  show (∫ α, ∏ P ∈ C, colRe ρ u u P α
    ∂(Measure.pi fun _ : LayerSite N => μG)) = 1
  rw [h1]
  simp [Measure.real]

/-- At `d = 1` with `ρ` trivial, `Φ` vanishes on the
nose: every summand is `quadReMoment - e1 ^ 4 = 1 - 1`. -/
theorem phiFunctional_eq_zero_of_dim_one_trivial (hd : d = 1)
    (htriv : ∀ g, repMatrix ρ g = 1) (u : LayerLink N → G) :
    phiFunctional ρ μG u = 0 := by
  show ∑ C ∈ primitiveQuads, (quadReMoment ρ μG C u u - (e1 ρ μG) ^ 4) = 0
  apply Finset.sum_eq_zero
  intro C _
  rw [quadReMoment_eq_one_of_dim_one_trivial ρ μG hd htriv,
    e1_eq_one_of_dim_one_trivial ρ μG hd htriv]
  norm_num

end E1Pack

/-! ## §5a.2. The `C4` cycle ordering

PQ-0 pinned the pattern of a primitive quad at
`3 ≤ N` to `C4` at the level of split data (degree
sequence `(2, 2, 2, 2)`, no digon pair), but explicitly
left the single-cycle phrasing open. This section lands
it: the four columns can be ordered so that consecutive
columns share exactly the consecutive sites of a
4-cycle. The walk is forced by primitivity itself:
each column's head site lies on a second column, and
the digon-freeness of `HasPatternC4` keeps the walk from
ever folding back onto a column or a site already seen.
The one step that is not a direct digon contradiction
is `s₃ ≠ s₀`: there the three incident pairs already
forced (`{P₀, P₂}` at `s₀` in the folded branch,
`{P₀, P₁}` at `s₁`, `{P₁, P₂}` at `s₂`) leave the
fourth column's base no site of the first three columns
to sit on, against the degree-`2` lower bound for
primitive quads. -/

section C4Ordering

variable {N : ℕ} [NeZero N]

/-- A column has a second site: at even `N` its two
sites are distinct (`card_colSites_two`), so from one
of them the other exists. -/
private theorem exists_other_site (hN : Even N) (Q : LayerColumn N)
    {s : LayerSite N} (hs : s ∈ colSites Q) :
    ∃ s', colSites Q = {s, s'} ∧ s' ≠ s := by
  have hcard := card_colSites_two hN Q
  rw [Finset.card_eq_two] at hcard
  obtain ⟨a, b, hab, hset⟩ := hcard
  rw [hset] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact ⟨b, hset, Ne.symm hab⟩
  · exact ⟨a, by rw [hset, Finset.pair_comm], hab⟩

/-- At a degree-`2` site, two known distinct incident
columns are all of them: the incident filter contains
the pair and has card `2`, so it equals the pair. -/
private theorem incident_pair_of_degree_two {C : Finset (LayerColumn N)}
    {s : LayerSite N} (hdeg : siteDegree C s = 2) {A B : LayerColumn N}
    (hA : A ∈ C) (hAs : s ∈ colSites A) (hB : B ∈ C) (hBs : s ∈ colSites B)
    (hAB : A ≠ B) :
    ∀ R ∈ C, s ∈ colSites R → R = A ∨ R = B := by
  have hsub : ({A, B} : Finset (LayerColumn N))
      ⊆ C.filter (fun P => s ∈ colSites P) := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rw [Finset.mem_filter]
    rcases hX with rfl | rfl
    · exact ⟨hA, hAs⟩
    · exact ⟨hB, hBs⟩
  have heq : C.filter (fun P => s ∈ colSites P) = {A, B} :=
    (Finset.eq_of_subset_of_card_le hsub
      (hdeg.trans (Finset.card_pair hAB).symm).le).symm
  intro R hRC hRs
  have hR : R ∈ C.filter (fun P => s ∈ colSites P) :=
    Finset.mem_filter.mpr ⟨hRC, hRs⟩
  rw [heq] at hR
  simpa using hR

/-- **The `C4` cycle ordering.** At `(Even N, 3 ≤ N)`,
every primitive quad `C` admits site and column
orderings `s, P : Fin 4 → _`, both injective, covering
`C`, with `colSites (P i) = {s i, s (i + 1)}` for every
`i` (indices mod `4`): the sharing multigraph of `C` is
a single 4-cycle, in the ordered form §5b consumes. -/
theorem c4_cycle_ordering (hN : Even N) (hN3 : 3 ≤ N)
    {C : Finset (LayerColumn N)} (hCmem : C ∈ primitiveQuads) :
    ∃ (s : Fin 4 → LayerSite N) (P : Fin 4 → LayerColumn N),
      Function.Injective s ∧ Function.Injective P
      ∧ (∀ i, P i ∈ C) ∧ (∀ Q ∈ C, ∃ i, P i = Q)
      ∧ ∀ i, colSites (P i) = {s i, s (i + 1)} := by
  have hC : IsPrimitiveQuad C := isPrimitiveQuad_of_mem hCmem
  have hCcard : C.card = 4 := hC.1
  have hC4 : HasPatternC4 C := (primitive_pattern_eq_C4 hN hN3 hCmem).1
  obtain ⟨P₀, hP₀⟩ : ∃ P, P ∈ C :=
    Finset.card_pos.mp (by omega : 0 < C.card)
  obtain ⟨s₁, hs₁, hs₁ne⟩ := exists_other_site hN P₀ (s := P₀.1) (by
    rw [mem_colSites]; exact Or.inl rfl)
  obtain ⟨P₁, hP₁, hP₁ne, hs₁P₁⟩ := hC.2 P₀ hP₀ s₁ (by
    rw [hs₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨s₂, hs₂, hs₂ne⟩ := exists_other_site hN P₁ hs₁P₁
  have hs₂ne₀ : s₂ ≠ P₀.1 := by
    intro hcon
    apply hC4.2
    refine ⟨P₀, hP₀, P₁, hP₁, hP₁ne.symm, ?_⟩
    rw [hs₁, hs₂, hcon, Finset.pair_comm]
  obtain ⟨P₂, hP₂, hP₂ne, hs₂P₂⟩ := hC.2 P₁ hP₁ s₂ (by
    rw [hs₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨s₃, hs₃, hs₃ne⟩ := exists_other_site hN P₂ hs₂P₂
  have hs₃ne₁ : s₃ ≠ s₁ := by
    intro hcon
    apply hC4.2
    refine ⟨P₁, hP₁, P₂, hP₂, hP₂ne.symm, ?_⟩
    rw [hs₂, hs₃, hcon, Finset.pair_comm]
  have hP₂ne₀ : P₂ ≠ P₀ := by
    intro hcon
    have hmem : s₂ ∈ colSites P₀ := by
      rw [← hcon, hs₃]
      exact Finset.mem_insert_self _ _
    rw [hs₁] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hs₂ne₀ h
    · exact hs₂ne h
  have hsupp01 : P₀.1 ∈ quadSupport C :=
    Finset.subset_biUnion_of_mem colSites hP₀ (by
      rw [mem_colSites]; exact Or.inl rfl)
  have hsupp1 : s₁ ∈ quadSupport C :=
    Finset.subset_biUnion_of_mem colSites hP₀ (by
      rw [hs₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsupp2 : s₂ ∈ quadSupport C :=
    Finset.subset_biUnion_of_mem colSites hP₁ (by
      rw [hs₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsupp3 : s₃ ∈ quadSupport C :=
    Finset.subset_biUnion_of_mem colSites hP₂ (by
      rw [hs₃]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have pairS1 := incident_pair_of_degree_two (C := C) (s := s₁)
    (hC4.1.2 _ hsupp1) hP₀
    (by rw [hs₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    hP₁ (by rw [hs₂]; exact Finset.mem_insert_self _ _) (Ne.symm hP₁ne)
  have pairS2 := incident_pair_of_degree_two (C := C) (s := s₂)
    (hC4.1.2 _ hsupp2) hP₁
    (by rw [hs₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    hP₂ (by rw [hs₃]; exact Finset.mem_insert_self _ _) (Ne.symm hP₂ne)
  have hsub3 : ({P₀, P₁, P₂} : Finset (LayerColumn N)) ⊆ C := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact hP₀
    · exact hP₁
    · exact hP₂
  have h0ni : P₀ ∉ ({P₁, P₂} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hP₁ne, Ne.symm hP₂ne₀⟩
  have h1ni : P₁ ∉ ({P₂} : Finset (LayerColumn N)) := by
    simp only [Finset.mem_singleton]
    exact Ne.symm hP₂ne
  have hcard3 : ({P₀, P₁, P₂} : Finset (LayerColumn N)).card = 3 := by
    rw [Finset.card_insert_of_notMem h0ni, Finset.card_insert_of_notMem h1ni,
      Finset.card_singleton]
  obtain ⟨P₃, hP₃sd⟩ : ∃ P, P ∈ C \ {P₀, P₁, P₂} := by
    have h := Finset.card_sdiff_add_card_eq_card hsub3
    rw [hCcard, hcard3] at h
    exact Finset.card_pos.mp (by omega : 0 < (C \ {P₀, P₁, P₂}).card)
  rw [Finset.mem_sdiff] at hP₃sd
  obtain ⟨hP₃, hP₃ni⟩ := hP₃sd
  have hP₃ne : P₃ ≠ P₀ ∧ P₃ ≠ P₁ ∧ P₃ ≠ P₂ := by
    have h := hP₃ni
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h
  have hsub4 : ({P₀, P₁, P₂, P₃} : Finset (LayerColumn N)) ⊆ C := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact hP₀
    · exact hP₁
    · exact hP₂
    · exact hP₃
  have hcard4 : ({P₀, P₁, P₂, P₃} : Finset (LayerColumn N)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hP₁ne, Ne.symm hP₂ne₀, Ne.symm hP₃ne.1⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hP₂ne, Ne.symm hP₃ne.2.1⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact Ne.symm hP₃ne.2.2), Finset.card_singleton]
  have hCeq : C = {P₀, P₁, P₂, P₃} :=
    (Finset.eq_of_subset_of_card_le hsub4 (by omega)).symm
  have hs₃ne₀ : s₃ ≠ P₀.1 := by
    intro hse
    have pair01 := incident_pair_of_degree_two (C := C) (s := P₀.1)
      (hC4.1.2 _ hsupp01) hP₀
      (by rw [mem_colSites]; exact Or.inl rfl)
      hP₂ (by rw [hs₃, hse]; exact
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (Ne.symm hP₂ne₀)
    have hsite_mem : ∀ x ∈ colSites P₃, x = P₀.1 ∨ x = s₁ ∨ x = s₂ := by
      intro x hx
      by_contra hcon
      push_neg at hcon
      obtain ⟨R, hRf, hRne⟩ :
          ∃ R ∈ C.filter (fun P => x ∈ colSites P), R ≠ P₃ := by
        by_contra hcon2
        push_neg at hcon2
        have hsub : C.filter (fun P => x ∈ colSites P) ⊆ {P₃} := by
          intro Y hY
          rw [Finset.mem_singleton]
          by_contra hne
          exact hne (hcon2 Y hY)
        have hle := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hle
        have hdeg2 : 2 ≤ (C.filter fun P => x ∈ colSites P).card :=
          two_le_siteDegree hC (Finset.subset_biUnion_of_mem colSites hP₃ hx)
        omega
      rw [Finset.mem_filter] at hRf
      obtain ⟨hRC, hxR⟩ := hRf
      rw [hCeq] at hRC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRC
      rcases hRC with rfl | rfl | rfl | rfl
      · rw [hs₁] at hxR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxR
        rcases hxR with h | h
        · exact hcon.1 h
        · exact hcon.2.1 h
      · rw [hs₂] at hxR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxR
        rcases hxR with h | h
        · exact hcon.2.1 h
        · exact hcon.2.2 h
      · rw [hs₃] at hxR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxR
        rcases hxR with h | h
        · exact hcon.2.2 h
        · exact hcon.1 (h.trans hse)
      · exact hRne rfl
    have hbmem : P₃.1 ∈ colSites P₃ := by
      rw [mem_colSites]; exact Or.inl rfl
    rcases hsite_mem P₃.1 hbmem with hb | hb | hb
    · rcases pair01 P₃ hP₃ (by rw [← hb]; exact hbmem) with h | h
      · exact hP₃ne.1 h
      · exact hP₃ne.2.2 h
    · rcases pairS1 P₃ hP₃ (by rw [← hb]; exact hbmem) with h | h
      · exact hP₃ne.1 h
      · exact hP₃ne.2.1 h
    · rcases pairS2 P₃ hP₃ (by rw [← hb]; exact hbmem) with h | h
      · exact hP₃ne.2.1 h
      · exact hP₃ne.2.2 h
  have hcardS : ({P₀.1, s₁, s₂, s₃} : Finset (LayerSite N)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hs₁ne, Ne.symm hs₂ne₀, Ne.symm hs₃ne₀⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hs₂ne, Ne.symm hs₃ne₁⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact Ne.symm hs₃ne), Finset.card_singleton]
  have hsupp : quadSupport C = {P₀.1, s₁, s₂, s₃} := by
    have hsub : ({P₀.1, s₁, s₂, s₃} : Finset (LayerSite N)) ⊆ quadSupport C := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hsupp01
      · exact hsupp1
      · exact hsupp2
      · exact hsupp3
    exact (Finset.eq_of_subset_of_card_le hsub (by
      rw [hcardS]; exact hC4.1.1.le)).symm
  have hbmem0 : P₃.1 ∈ colSites P₃ := by
    rw [mem_colSites]; exact Or.inl rfl
  obtain ⟨t, ht, htne⟩ := exists_other_site hN P₃ (s := P₃.1) hbmem0
  have htmem : t ∈ colSites P₃ := by
    rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have htsupp : t ∈ quadSupport C :=
    Finset.subset_biUnion_of_mem colSites hP₃ htmem
  have hbsupp : P₃.1 ∈ quadSupport C :=
    Finset.subset_biUnion_of_mem colSites hP₃ hbmem0
  rw [hsupp] at htsupp hbsupp
  simp only [Finset.mem_insert, Finset.mem_singleton] at htsupp hbsupp
  have ht' : t = P₀.1 ∨ t = s₃ := by
    rcases htsupp with h | h | h | h
    · exact Or.inl h
    · have hinc : s₁ ∈ colSites P₃ := by rw [← h]; exact htmem
      rcases pairS1 P₃ hP₃ hinc with hP | hP
      · exact (hP₃ne.1 hP).elim
      · exact (hP₃ne.2.1 hP).elim
    · have hinc : s₂ ∈ colSites P₃ := by rw [← h]; exact htmem
      rcases pairS2 P₃ hP₃ hinc with hP | hP
      · exact (hP₃ne.2.1 hP).elim
      · exact (hP₃ne.2.2 hP).elim
    · exact Or.inr h
  have hb' : P₃.1 = P₀.1 ∨ P₃.1 = s₃ := by
    rcases hbsupp with h | h | h | h
    · exact Or.inl h
    · have hinc : s₁ ∈ colSites P₃ := by rw [← h]; exact hbmem0
      rcases pairS1 P₃ hP₃ hinc with hP | hP
      · exact (hP₃ne.1 hP).elim
      · exact (hP₃ne.2.1 hP).elim
    · have hinc : s₂ ∈ colSites P₃ := by rw [← h]; exact hbmem0
      rcases pairS2 P₃ hP₃ hinc with hP | hP
      · exact (hP₃ne.2.1 hP).elim
      · exact (hP₃ne.2.2 hP).elim
    · exact Or.inr h
  have hsites₃ : colSites P₃ = {P₀.1, s₃} := by
    rcases hb' with hb | hb <;> rcases ht' with htq | htq
    · exact absurd (htq.trans hb.symm) htne
    · rw [ht, hb, htq]
    · rw [ht, hb, htq, Finset.pair_comm]
    · exact absurd (htq.trans hb.symm) htne
  refine ⟨![P₀.1, s₁, s₂, s₃], ![P₀, P₁, P₂, P₃], ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hs₁ne, hs₂ne, hs₂ne₀, hs₃ne, hs₃ne₁, hs₃ne₀,
        hs₁ne.symm, hs₂ne.symm, hs₂ne₀.symm, hs₃ne.symm, hs₃ne₁.symm,
        hs₃ne₀.symm] at hij <;> rfl
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hP₁ne, hP₂ne, hP₂ne₀, hP₃ne.1, hP₃ne.2.1, hP₃ne.2.2,
        hP₁ne.symm, hP₂ne.symm, hP₂ne₀.symm, hP₃ne.1.symm, hP₃ne.2.1.symm,
        hP₃ne.2.2.symm] at hij <;> rfl
  · intro i
    fin_cases i <;> simp [hP₀, hP₁, hP₂, hP₃]
  · intro Q hQ
    rw [hCeq] at hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
  · intro i
    fin_cases i <;> simp [hs₁, hs₂, hs₃, hsites₃, Finset.pair_comm]

end C4Ordering


/-! ## §5a.3. The split-list check (pre-registered K-PW-5-1)

On the ordering of §5a.2, each column is either forward
(base at `s i`, head at `s (i + 1)`) or backward. The split
at `s j` is `(1, 1)` unless the bits of the two incident
columns flip there: a `B`-to-`F` flip makes a source
`(2, 0)`, an `F`-to-`B` flip a sink `(0, 2)`. Around the
4-cycle the flips of the two kinds alternate, so the
possible split lists are: all `(1, 1)` (constant bits);
one source and one sink **opposite** each other (two runs);
two sources and two sinks alternating; or one source and
one sink **adjacent** (runs of length `3` and `1`). The
last two shapes are killed by the step arithmetic of the
layer: writing each column's head as its base plus a
`Pi.single` step (the four head equations), the alternating
shape forces a `2 = 2` step identity
`single ν₀ + single ν₂ = single ν₁ + single ν₃` whose two
solutions each identify two columns or two sites
(`single_pair_eq_imp`), and the adjacent shape forces a
`1 = 3` step identity — one step equal to a sum of three —
which has no solution at `3 ≤ N` since coordinate masses
`1` and `3` differ mod `N` (`single_ne_sum_three`). What
survives is exactly the scoping's list: `WRAP` (all
`(1, 1)`) and `PLAQ` (source and sink opposite). -/

section SplitList

variable {N : ℕ} [NeZero N]

/-- A `Pi.single` step read at a coordinate: the value is
`1` at its own coordinate and `0` elsewhere. -/
private theorem single_apply_eq (x y : Fin 4) :
    (Pi.single x (1 : ZMod N) : Fin 4 → ZMod N) y
      = if y = x then 1 else 0 := by
  by_cases h : y = x
  · rw [if_pos h, h, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

/-- The coordinate mass of a single step is `1`. -/
private theorem sum_single_apply (x : Fin 4) :
    (∑ j : Fin 4, (Pi.single x (1 : ZMod N) : Fin 4 → ZMod N) j) = 1 := by
  have h1 : (∑ j : Fin 4, (Pi.single x (1 : ZMod N) : Fin 4 → ZMod N) j)
      = (Pi.single x (1 : ZMod N) : Fin 4 → ZMod N) x := by
    refine Finset.sum_eq_single x ?_ ?_
    · intro j _ hjx
      rw [Pi.single_eq_of_ne hjx]
    · intro h
      exact (h (Finset.mem_univ x)).elim
  rw [h1, Pi.single_eq_same]

/-- `(1 : ZMod N) + 1 ≠ 0` at `3 ≤ N`. -/
private theorem two_ne_zero_zmod (hN3 : 3 ≤ N) :
    (1 : ZMod N) + 1 ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod N) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hle : N ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

/-- `(1 : ZMod N) + 1 + 1 ≠ 1` at `3 ≤ N` (i.e. `3 ≠ 1`
in `ZMod N`: `3 ≡ 1 [MOD N]` would force `N ∣ 2`). -/
private theorem three_ne_one_zmod (hN3 : 3 ≤ N) :
    (1 : ZMod N) + 1 + 1 ≠ 1 := by
  intro h
  have h2 : ((3 : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by exact_mod_cast h
  rw [ZMod.natCast_eq_natCast_iff] at h2
  have h3 : (3 : ℕ) % N = 1 % N := h2
  rcases Nat.eq_or_lt_of_le hN3 with hN | hN
  · subst hN
    norm_num at h3
  · rw [Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt (by omega : 1 < N)] at h3
    exact (by norm_num : (3 : ℕ) ≠ 1) h3

/-- **The `2 = 2` step identity, read at one end.** If
`single a + single c = single b + single d` in
`Fin 4 → ZMod N` at `3 ≤ N`, then `b = a` or `d = a`:
evaluating at the coordinate `a`, the right side is `0`
unless one of `b, d` hits `a`, while the left side is
`1` or `1 + 1`, both nonzero. -/
private theorem single_pair_eq_imp (hN3 : 3 ≤ N) {a b c d : Fin 4}
    (h : (Pi.single a (1 : ZMod N) : Fin 4 → ZMod N)
          + (Pi.single c (1 : ZMod N) : Fin 4 → ZMod N)
        = (Pi.single b (1 : ZMod N) : Fin 4 → ZMod N)
          + (Pi.single d (1 : ZMod N) : Fin 4 → ZMod N)) :
    b = a ∨ d = a := by
  by_contra hcon
  push_neg at hcon
  have ha := congrFun h a
  rw [Pi.add_apply, Pi.add_apply, single_apply_eq, single_apply_eq,
    single_apply_eq, single_apply_eq] at ha
  rw [if_neg (Ne.symm hcon.1), if_neg (Ne.symm hcon.2), add_zero,
    if_pos rfl] at ha
  by_cases hca : a = c
  · rw [if_pos hca] at ha
    exact two_ne_zero_zmod hN3 ha
  · rw [if_neg hca, add_zero] at ha
    exact one_ne_zero_zmod (by omega : 2 ≤ N) ha

/-- **No step is a sum of three steps.** If
`single a = single b + single c + single d` in
`Fin 4 → ZMod N` at `3 ≤ N`, summing all coordinates
gives `1 = 1 + 1 + 1` in `ZMod N`, i.e. `3 = 1`, which
fails since `N ∤ 2`. -/
private theorem single_ne_sum_three (hN3 : 3 ≤ N) {a b c d : Fin 4}
    (h : (Pi.single a (1 : ZMod N) : Fin 4 → ZMod N)
        = (Pi.single b (1 : ZMod N) : Fin 4 → ZMod N)
          + (Pi.single c (1 : ZMod N) : Fin 4 → ZMod N)
          + (Pi.single d (1 : ZMod N) : Fin 4 → ZMod N)) : False := by
  have hsum := congrArg (fun f : Fin 4 → ZMod N => ∑ j : Fin 4, f j) h
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single_apply] at hsum
  exact three_ne_one_zmod hN3 hsum.symm

/-- On the cycle ordering, every column is forward or
backward: its base is one of the two sites it reads, and
its head is the other (base and head differ at even `N`). -/
private theorem base_head_cases (hN : Even N) (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)}) (i : Fin 4) :
    ((P i).1 = s i ∧ layerShift (P i).2.1 (P i).2.2 (P i).1 = s (i + 1))
    ∨ ((P i).1 = s (i + 1) ∧ layerShift (P i).2.1 (P i).2.2 (P i).1
        = s i) := by
  have hbase : (P i).1 ∈ colSites (P i) := by
    rw [mem_colSites]; exact Or.inl rfl
  have hhead : layerShift (P i).2.1 (P i).2.2 (P i).1 ∈ colSites (P i) := by
    rw [mem_colSites]; exact Or.inr rfl
  rw [hinc i] at hbase hhead
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbase hhead
  have hne : layerShift (P i).2.1 (P i).2.2 (P i).1 ≠ (P i).1 :=
    layerShift_ne_self hN _ _ _
  rcases hbase with hb | hb
  · refine Or.inl ⟨hb, ?_⟩
    rcases hhead with hh | hh
    · exact absurd (hh.trans hb.symm) hne
    · exact hh
  · refine Or.inr ⟨hb, ?_⟩
    rcases hhead with hh | hh
    · exact hh
    · exact absurd (hh.trans hb.symm) hne

/-- The based-count at a site with a known incident pair:
the first component of `siteSplit` is the sum of the two
incidence indicators of the pair. -/
private theorem siteSplit_fst_of_incident_pair {C : Finset (LayerColumn N)}
    {s : LayerSite N} (hdeg : siteDegree C s = 2) {A B : LayerColumn N}
    (hAB : A ≠ B) (hpair : ∀ R ∈ C, s ∈ colSites R → R = A ∨ R = B)
    (hA : A ∈ C) (hB : B ∈ C) :
    (siteSplit C s).1
      = (if A.1 = s then 1 else 0) + (if B.1 = s then 1 else 0) := by
  classical
  have hfilter : C.filter (fun P => P.1 = s)
      = Finset.filter (fun P => P.1 = s) ({A, B} : Finset (LayerColumn N)) := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hRC, hRs⟩
      have hinc : s ∈ colSites R := by
        rw [mem_colSites]; exact Or.inl hRs.symm
      exact ⟨hpair R hRC hinc, hRs⟩
    · rintro ⟨hRAB, hRs⟩
      refine ⟨?_, hRs⟩
      rcases hRAB with rfl | rfl
      · exact hA
      · exact hB
  show (C.filter (fun P => P.1 = s)).card = _
  rw [hfilter, Finset.filter_insert, Finset.filter_singleton]
  by_cases hA' : A.1 = s <;> by_cases hB' : B.1 = s <;>
    simp [hA', hB', hAB]

/-- A `C4` site's split is determined by its based-count
`n`: the split is `(n, 2 - n)`, since the two components
sum to the degree `2` (`siteSplit_add`). -/
private theorem siteSplit_eq_of_fst (hN : Even N) {C : Finset (LayerColumn N)}
    {s : LayerSite N} (hdeg : siteDegree C s = 2) {n : ℕ}
    (h1 : (siteSplit C s).1 = n) :
    siteSplit C s = (n, 2 - n) := by
  have hadd := siteSplit_add hN C s
  rw [hdeg] at hadd
  refine Prod.ext h1 ?_
  omega

end SplitList

section SplitListCorollary

variable {N : ℕ} [NeZero N]

/-- **The split-list check (K-PW-5-1 does not fire).** For
every primitive quad `C` at `(Even N, 3 ≤ N)`, on the
cycle ordering of §5a.2 the list of splits over the four
support sites (in cyclic order) is exactly one of the
scoping's two patterns:

* `WRAP`: all four splits are `(1, 1)`; or
* `PLAQ`: for some cyclic position `k`, the splits are
  `(2, 0)` at `s k`, `(1, 1)` at `s (k + 1)`, `(0, 2)` at
  `s (k + 2)`, `(1, 1)` at `s (k + 3)` — the source and
  the sink sit at OPPOSITE corners of the cycle.

The proof runs the `16` forward/backward bit patterns of
the four columns: the constant patterns give `WRAP`, the
two-run patterns give `PLAQ`, the alternating patterns
die by `single_pair_eq_imp` (a `2 = 2` step identity
forcing two columns or two sites to coincide), and the
adjacent source/sink patterns die by
`single_ne_sum_three` (the length-`1` path and the
length-`3` path between the same two sites would force
one step to equal a sum of three). -/
theorem c4_split_list (hN : Even N) (hN3 : 3 ≤ N)
    {C : Finset (LayerColumn N)} (hCmem : C ∈ primitiveQuads) :
    ∃ (s : Fin 4 → LayerSite N) (P : Fin 4 → LayerColumn N),
      Function.Injective s ∧ (∀ i, P i ∈ C) ∧ (∀ Q ∈ C, ∃ i, P i = Q)
      ∧ (∀ i, colSites (P i) = {s i, s (i + 1)})
      ∧ ((∀ j, siteSplit C (s j) = (1, 1))
        ∨ ∃ k : Fin 4, siteSplit C (s k) = (2, 0)
            ∧ siteSplit C (s (k + 1)) = (1, 1)
            ∧ siteSplit C (s (k + 2)) = (0, 2)
            ∧ siteSplit C (s (k + 3)) = (1, 1)) := by
  obtain ⟨s, P, hs_inj, hP_inj, hPmem, hPcover, hinc⟩ :=
    c4_cycle_ordering hN hN3 hCmem
  refine ⟨s, P, hs_inj, hPmem, hPcover, hinc, ?_⟩
  have hC4 : HasPatternC4 C := (primitive_pattern_eq_C4 hN hN3 hCmem).1
  have hsmem : ∀ j, s j ∈ quadSupport C := fun j =>
    Finset.subset_biUnion_of_mem colSites (hPmem j) (by
      rw [hinc j]; exact Finset.mem_insert_self _ _)
  have hdeg : ∀ j, siteDegree C (s j) = 2 :=
    fun j => hC4.1.2 _ (hsmem j)
  have hne3 : ∀ j : Fin 4, j + 3 ≠ j := by decide
  have h43 : ∀ j : Fin 4, j + 3 + 1 = j := by decide
  have hpair : ∀ j, ∀ R ∈ C, s j ∈ colSites R → R = P (j + 3) ∨ R = P j := by
    intro j
    refine incident_pair_of_degree_two (hdeg j) (hPmem _) ?_ (hPmem _) ?_
      (Function.Injective.ne hP_inj (hne3 j))
    · rw [hinc (j + 3), h43 j]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [hinc j]
      exact Finset.mem_insert_self _ _
  have hfst : ∀ j, (siteSplit C (s j)).1
      = (if (P (j + 3)).1 = s j then 1 else 0)
        + (if (P j).1 = s j then 1 else 0) :=
    fun j => siteSplit_fst_of_incident_pair (hdeg j)
      (Function.Injective.ne hP_inj (hne3 j)) (hpair j) (hPmem _) (hPmem _)
  have heq : ∀ i, (layerShift (P i).2.1 (P i).2.2 (P i).1).1
      = Pi.single (P i).2.1 (1 : ZMod N) + ((P i).1).1 := by
    intro i
    rw [layerShift_coe, torusShift_apply]
  have hne01 : s 0 ≠ s 1 := Function.Injective.ne hs_inj (by decide)
  have hne02 : s 0 ≠ s 2 := Function.Injective.ne hs_inj (by decide)
  have hne03 : s 0 ≠ s 3 := Function.Injective.ne hs_inj (by decide)
  have hne12 : s 1 ≠ s 2 := Function.Injective.ne hs_inj (by decide)
  have hne13 : s 1 ≠ s 3 := Function.Injective.ne hs_inj (by decide)
  have hne23 : s 2 ≠ s 3 := Function.Injective.ne hs_inj (by decide)
  have e03 : (0 : Fin 4) + 3 = 3 := by decide
  have e13 : (1 : Fin 4) + 3 = 0 := by decide
  have e23 : (2 : Fin 4) + 3 = 1 := by decide
  have e33 : (3 : Fin 4) + 3 = 2 := by decide
  have e01 : (0 : Fin 4) + 1 = 1 := by decide
  have e11 : (1 : Fin 4) + 1 = 2 := by decide
  have e21 : (2 : Fin 4) + 1 = 3 := by decide
  have e31 : (3 : Fin 4) + 1 = 0 := by decide
  have hf0 := hfst 0
  have hf1 := hfst 1
  have hf2 := hfst 2
  have hf3 := hfst 3
  rw [e03] at hf0
  rw [e13] at hf1
  rw [e23] at hf2
  rw [e33] at hf3
  have hb0 := base_head_cases hN s P hinc 0
  have hb1 := base_head_cases hN s P hinc 1
  have hb2 := base_head_cases hN s P hinc 2
  have hb3 := base_head_cases hN s P hinc 3
  rw [e01] at hb0
  rw [e11] at hb1
  rw [e21] at hb2
  rw [e31] at hb3
  rcases hb0 with ⟨hb0, hh0⟩ | ⟨hb0, hh0⟩ <;>
    rcases hb1 with ⟨hb1, hh1⟩ | ⟨hb1, hh1⟩ <;>
    rcases hb2 with ⟨hb2, hh2⟩ | ⟨hb2, hh2⟩ <;>
    rcases hb3 with ⟨hb3, hh3⟩ | ⟨hb3, hh3⟩
  · -- FFFF: all forward — WRAP.
    have f0 : (siteSplit C (s 0)).1 = 1 := by
      rw [hf0]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f1 : (siteSplit C (s 1)).1 = 1 := by
      rw [hf1]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f2 : (siteSplit C (s 2)).1 = 1 := by
      rw [hf2]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f3 : (siteSplit C (s 3)).1 = 1 := by
      rw [hf3]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have sp0 : siteSplit C (s 0) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 0) f0
    have sp1 : siteSplit C (s 1) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 1) f1
    have sp2 : siteSplit C (s 2) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 2) f2
    have sp3 : siteSplit C (s 3) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 3) f3
    refine Or.inl (fun j => ?_)
    fin_cases j
    · exact sp0
    · exact sp1
    · exact sp2
    · exact sp3
  · -- FFFB: source at `s 0`, sink at `s 3`, adjacent — killed.
    have e0 : (s 1).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 0).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 2).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 1).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 3).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 2).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 3).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 0).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 3).1 = (Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N)) + (s 0).1 := by
      rw [e2, e1, e0]; abel
    have key :=
      add_right_cancel_iff.mp (e3.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- FFBF: source at `s 3`, sink at `s 2`, adjacent — killed.
    have e0 : (s 1).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 0).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 2).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 1).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 2).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 3).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 0).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 3).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 2).1 = (Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N)) + (s 3).1 := by
      rw [e1, e0, e3]; abel
    have key :=
      add_right_cancel_iff.mp (e2.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- FFBB: PLAQ with source at `s 0`, sink at `s 2`.
    have f0 : (siteSplit C (s 0)).1 = 2 := by
      rw [hf0]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f1 : (siteSplit C (s 1)).1 = 1 := by
      rw [hf1]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f2 : (siteSplit C (s 2)).1 = 0 := by
      rw [hf2]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f3 : (siteSplit C (s 3)).1 = 1 := by
      rw [hf3]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have sp0 : siteSplit C (s 0) = (2, 2 - 2) :=
      siteSplit_eq_of_fst hN (hdeg 0) f0
    have sp1 : siteSplit C (s 1) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 1) f1
    have sp2 : siteSplit C (s 2) = (0, 2 - 0) :=
      siteSplit_eq_of_fst hN (hdeg 2) f2
    have sp3 : siteSplit C (s 3) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 3) f3
    exact Or.inr ⟨0, sp0, sp1, sp2, sp3⟩
  · -- FBFF: source at `s 2`, sink at `s 1`, adjacent — killed.
    have e0 : (s 1).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 0).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 1).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 2).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 3).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 2).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 0).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 3).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 1).1 = (Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N)) + (s 2).1 := by
      rw [e0, e3, e2]; abel
    have key :=
      add_right_cancel_iff.mp (e1.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- FBFB: alternating sources/sinks — killed by the pair identity.
    have e0 : (s 1).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 0).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 1).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 2).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 3).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 2).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 3).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 0).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have e02 : (s 1).1 + (s 3).1 = Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N) + ((s 0).1 + (s 2).1) := by
      linear_combination e0 + e2
    have e13 : (s 1).1 + (s 3).1 = Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N) + ((s 0).1 + (s 2).1) := by
      linear_combination e1 + e3
    have key :=
      add_right_cancel_iff.mp (e02.symm.trans e13)
    rcases single_pair_eq_imp hN3 key with hν | hν
    · rw [hν] at e1
      have hsite : (s 0).1 = (s 2).1 :=
        add_left_cancel_iff.mp (e0.symm.trans e1)
      exact (hne02 (Subtype.ext hsite)).elim
    · have hPeq : P 3 = P 0 := Prod.ext (hb3.trans hb0.symm) (Subtype.ext hν)
      exact ((show (3 : Fin 4) ≠ 0 by decide) (hP_inj hPeq)).elim
  · -- FBBF: PLAQ with source at `s 3`, sink at `s 1`.
    have f0 : (siteSplit C (s 0)).1 = 1 := by
      rw [hf0]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f1 : (siteSplit C (s 1)).1 = 0 := by
      rw [hf1]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f2 : (siteSplit C (s 2)).1 = 1 := by
      rw [hf2]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f3 : (siteSplit C (s 3)).1 = 2 := by
      rw [hf3]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have sp0 : siteSplit C (s 0) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 0) f0
    have sp1 : siteSplit C (s 1) = (0, 2 - 0) :=
      siteSplit_eq_of_fst hN (hdeg 1) f1
    have sp2 : siteSplit C (s 2) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 2) f2
    have sp3 : siteSplit C (s 3) = (2, 2 - 2) :=
      siteSplit_eq_of_fst hN (hdeg 3) f3
    exact Or.inr ⟨3, sp3, sp0, sp1, sp2⟩
  · -- FBBB: source at `s 0`, sink at `s 1`, adjacent — killed.
    have e0 : (s 1).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 0).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 1).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 2).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 2).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 3).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 3).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 0).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 1).1 = (Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N)) + (s 0).1 := by
      rw [e1, e2, e3]; abel
    have key :=
      add_right_cancel_iff.mp (e0.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- BFFF: source at `s 1`, sink at `s 0`, adjacent — killed.
    have e0 : (s 0).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 1).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 2).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 1).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 3).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 2).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 0).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 3).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 0).1 = (Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N)) + (s 1).1 := by
      rw [e3, e2, e1]; abel
    have key :=
      add_right_cancel_iff.mp (e0.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- BFFB: PLAQ with source at `s 1`, sink at `s 3`.
    have f0 : (siteSplit C (s 0)).1 = 1 := by
      rw [hf0]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f1 : (siteSplit C (s 1)).1 = 2 := by
      rw [hf1]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f2 : (siteSplit C (s 2)).1 = 1 := by
      rw [hf2]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f3 : (siteSplit C (s 3)).1 = 0 := by
      rw [hf3]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have sp0 : siteSplit C (s 0) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 0) f0
    have sp1 : siteSplit C (s 1) = (2, 2 - 2) :=
      siteSplit_eq_of_fst hN (hdeg 1) f1
    have sp2 : siteSplit C (s 2) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 2) f2
    have sp3 : siteSplit C (s 3) = (0, 2 - 0) :=
      siteSplit_eq_of_fst hN (hdeg 3) f3
    exact Or.inr ⟨1, sp1, sp2, sp3, sp0⟩
  · -- BFBF: alternating sources/sinks — killed by the pair identity.
    have e0 : (s 0).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 1).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 2).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 1).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 2).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 3).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 0).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 3).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have e02 : (s 0).1 + (s 2).1 = Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N) + ((s 1).1 + (s 3).1) := by
      linear_combination e1 + e3
    have e13 : (s 0).1 + (s 2).1 = Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N) + ((s 1).1 + (s 3).1) := by
      linear_combination e0 + e2
    have key :=
      add_right_cancel_iff.mp (e02.symm.trans e13)
    rcases single_pair_eq_imp hN3 key with hν | hν
    · have hPeq : P 0 = P 1 := Prod.ext (hb0.trans hb1.symm) (Subtype.ext hν)
      exact ((show (0 : Fin 4) ≠ 1 by decide) (hP_inj hPeq)).elim
    · rw [hν] at e2
      have hsite : (s 1).1 = (s 3).1 :=
        add_left_cancel_iff.mp (e1.symm.trans e2)
      exact (hne13 (Subtype.ext hsite)).elim
  · -- BFBB: source at `s 1`, sink at `s 2`, adjacent — killed.
    have e0 : (s 0).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 1).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 2).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 1).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 2).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 3).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 3).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 0).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 2).1 = (Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N)) + (s 1).1 := by
      rw [e2, e3, e0]; abel
    have key :=
      add_right_cancel_iff.mp (e1.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- BBFF: PLAQ with source at `s 2`, sink at `s 0`.
    have f0 : (siteSplit C (s 0)).1 = 0 := by
      rw [hf0]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f1 : (siteSplit C (s 1)).1 = 1 := by
      rw [hf1]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f2 : (siteSplit C (s 2)).1 = 2 := by
      rw [hf2]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f3 : (siteSplit C (s 3)).1 = 1 := by
      rw [hf3]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have sp0 : siteSplit C (s 0) = (0, 2 - 0) :=
      siteSplit_eq_of_fst hN (hdeg 0) f0
    have sp1 : siteSplit C (s 1) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 1) f1
    have sp2 : siteSplit C (s 2) = (2, 2 - 2) :=
      siteSplit_eq_of_fst hN (hdeg 2) f2
    have sp3 : siteSplit C (s 3) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 3) f3
    exact Or.inr ⟨2, sp2, sp3, sp0, sp1⟩
  · -- BBFB: source at `s 2`, sink at `s 3`, adjacent — killed.
    have e0 : (s 0).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 1).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 1).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 2).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 3).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 2).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 3).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 0).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 3).1 = (Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 3).2.1 (1 : ZMod N)) + (s 2).1 := by
      rw [e3, e0, e1]; abel
    have key :=
      add_right_cancel_iff.mp (e2.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- BBBF: source at `s 3`, sink at `s 0`, adjacent — killed.
    have e0 : (s 0).1 = Pi.single (P 0).2.1 (1 : ZMod N) + (s 1).1 := by
      have h0 := heq 0
      rw [hh0, hb0] at h0
      exact h0
    have e1 : (s 1).1 = Pi.single (P 1).2.1 (1 : ZMod N) + (s 2).1 := by
      have h1 := heq 1
      rw [hh1, hb1] at h1
      exact h1
    have e2 : (s 2).1 = Pi.single (P 2).2.1 (1 : ZMod N) + (s 3).1 := by
      have h2 := heq 2
      rw [hh2, hb2] at h2
      exact h2
    have e3 : (s 0).1 = Pi.single (P 3).2.1 (1 : ZMod N) + (s 3).1 := by
      have h3 := heq 3
      rw [hh3, hb3] at h3
      exact h3
    have hlong : (s 0).1 = (Pi.single (P 0).2.1 (1 : ZMod N)
        + Pi.single (P 1).2.1 (1 : ZMod N)
        + Pi.single (P 2).2.1 (1 : ZMod N)) + (s 3).1 := by
      rw [e0, e1, e2]; abel
    have key :=
      add_right_cancel_iff.mp (e3.symm.trans hlong)
    exact (single_ne_sum_three hN3 key).elim
  · -- BBBB: all backward — WRAP.
    have f0 : (siteSplit C (s 0)).1 = 1 := by
      rw [hf0]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f1 : (siteSplit C (s 1)).1 = 1 := by
      rw [hf1]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f2 : (siteSplit C (s 2)).1 = 1 := by
      rw [hf2]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have f3 : (siteSplit C (s 3)).1 = 1 := by
      rw [hf3]
      simp only [hb0, hb1, hb2, hb3, hne01, hne02, hne03, hne12, hne13,
        hne23, Ne.symm hne01, Ne.symm hne02, Ne.symm hne03, Ne.symm hne12,
        Ne.symm hne13, Ne.symm hne23, eq_self_iff_true, ite_true, ite_false,
        zero_add, add_zero, one_add_one_eq_two]
    have sp0 : siteSplit C (s 0) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 0) f0
    have sp1 : siteSplit C (s 1) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 1) f1
    have sp2 : siteSplit C (s 2) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 2) f2
    have sp3 : siteSplit C (s 3) = (1, 2 - 1) :=
      siteSplit_eq_of_fst hN (hdeg 3) f3
    refine Or.inl (fun j => ?_)
    fin_cases j
    · exact sp0
    · exact sp1
    · exact sp2
    · exact sp3

end SplitListCorollary

/-! ## §5b. The contraction engine

PW-5b: the machinery that turns a `quadCharMoment` at a `C4`
quad into evaluated pair contractions. Three parts:

* **R1 (support factorization).** Each column character is
  expanded into matrix entries (`trace` of the column word as
  a four-fold entry sum). A column contributes exactly two
  site-local factors — one at its base, one at its head — and
  two frozen link factors. The stratum integral then factors
  over the sites of the layer: at every site outside the
  quad's support the local factor is `1`, and at each support
  site exactly the two incident columns contribute. The end
  form is a finite sum over entry-index assignments of a
  product of frozen factors times a product, over the four
  ordered support sites, of single-site Haar integrals of
  pairs of entry factors.
* **The per-site type table.** Each site factor is a plain or
  a conjugated `repMatrix` entry, determined by the column's
  pattern membership and by whether the site is the column's
  base or its head; the four pair evaluations (mixed by PW-1,
  same-orientation by PW-3) are packaged against the
  site-factor definitions, and the based/headed incidence at
  a site is read off its `siteSplit` value.
* **R2 (twisted contraction).** The entry-level sewing of
  frozen path sandwiches: contracting a path word against a
  conjugate path (mixed) or against a plain path
  (same-orientation) at one site, with the `J`-insertion of
  PW-3 appearing in the contracted object; and the final
  closure identity, which contracts the `star (J) · J` tensor
  around the closed cycle into a Frobenius pairing — a sum of
  entry products of the two `J`-twisted path matrices, hence
  a sum of squared norms when the second path is the
  conjugate of the first.

**Fences.** NO CLAIM; dials 0/4. This section is a
contraction engine only: it evaluates integrals and
rearranges finite sums, and asserts **no sign** for `Φ` or
for any moment. The assembly of the sign from these parts
is §5c. Finite-volume algebra only; `N = 2` is not touched.
-/

section ContractionEngine

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-! ### §5b.0. The site-factor definitions

For a column `Q` and a pattern bit `σ` (`σ = true`: the
column is taken plain in the moment; `σ = false`: taken
conjugated), the character of the column word is the sum,
over entry indices `a b e f`, of a product of two site-local
factors and one frozen factor:

* plain: `ρ(α c) a b · star (ρ(α σ_Q c)) f e · (ρ(u' ℓ) b e · star (ρ(u ℓ)) a f)`;
* conjugated: `star (ρ(α c)) a f · ρ(α σ_Q c) b e · (ρ(u ℓ) a b · star (ρ(u' ℓ)) f e)`,

where `c = Q.1` is the base, `σ_Q c` the head, and
`ℓ = layerLinkOf c Q.2.1 Q.2.2` the column's link. The two
site-local factors are packaged as `colBaseFac` (at the
base) and `colHeadFac` (at the head); `colSiteFac` selects
the factor a column contributes at a given site (`1` at
sites the column does not read). -/

/-- The link a column reads. -/
def colLink (Q : LayerColumn N) : LayerLink N :=
  layerLinkOf Q.1 Q.2.1 Q.2.2

/-- The head site of a column: the second site it reads. -/
def colHead (Q : LayerColumn N) : LayerSite N :=
  layerShift Q.2.1 Q.2.2 Q.1

/-- The two sites a column reads are its base and its head. -/
theorem colSites_eq (Q : LayerColumn N) :
    colSites Q = {Q.1, colHead Q} := rfl

/-- The site-local factor a column contributes at its
**base**: a plain entry of `ρ(g)` at indices `(a, b)` if the
column is taken plain; if taken conjugated, the base letter
of the inverse word is `(α c)⁻¹`, whose `(f, a)` entry is
the conjugate of the `(a, f)` entry of `ρ(g)`. -/
def colBaseFac (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d) (g : G) : ℂ :=
  if σ then repMatrix ρ g a b else star (repMatrix ρ g a f)

/-- The site-local factor a column contributes at its
**head**: if the column is taken plain, the head letter of
its word is `(α σ_Q c)⁻¹`, whose `(e, f)` entry is the
conjugate of the `(f, e)` entry of `ρ(g)`; if taken
conjugated, a plain entry at `(b, e)`. -/
def colHeadFac (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d) (g : G) : ℂ :=
  if σ then star (repMatrix ρ g f e) else repMatrix ρ g b e

/-- The frozen factor of a column: the two link entries of
its word, at the frozen configurations `u, u'`. -/
def colFrozenFac (u u' : LayerLink N → G) (Q : LayerColumn N) (σ : Bool)
    (a b e f : Fin d) : ℂ :=
  if σ then repMatrix ρ (u' (colLink Q)) b e
      * star (repMatrix ρ (u (colLink Q)) a f)
    else repMatrix ρ (u (colLink Q)) a b
      * star (repMatrix ρ (u' (colLink Q)) f e)

/-- The factor a column contributes at a site `r`: its base
factor at the base, its head factor at the head, and `1`
at any site it does not read. -/
noncomputable def colSiteFac (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d)
    (r : LayerSite N) (g : G) : ℂ :=
  if r = Q.1 then colBaseFac ρ Q σ a b e f g
  else if r = colHead Q then colHeadFac ρ Q σ a b e f g
  else 1

/-- The base factor at `σ = true`, unfolded. -/
private theorem colBaseFac_true (Q : LayerColumn N) (a b e f : Fin d)
    (g : G) :
    colBaseFac ρ Q true a b e f g = repMatrix ρ g a b := rfl

/-- The base factor at `σ = false`, unfolded. -/
private theorem colBaseFac_false (Q : LayerColumn N) (a b e f : Fin d)
    (g : G) :
    colBaseFac ρ Q false a b e f g = star (repMatrix ρ g a f) := rfl

/-- The head factor at `σ = true`, unfolded. -/
private theorem colHeadFac_true (Q : LayerColumn N) (a b e f : Fin d)
    (g : G) :
    colHeadFac ρ Q true a b e f g = star (repMatrix ρ g f e) := rfl

/-- The head factor at `σ = false`, unfolded. -/
private theorem colHeadFac_false (Q : LayerColumn N) (a b e f : Fin d)
    (g : G) :
    colHeadFac ρ Q false a b e f g = repMatrix ρ g b e := rfl

/-- The frozen factor at `σ = true`, unfolded. -/
private theorem colFrozenFac_true (u u' : LayerLink N → G)
    (Q : LayerColumn N) (a b e f : Fin d) :
    colFrozenFac ρ u u' Q true a b e f
      = repMatrix ρ (u' (colLink Q)) b e
        * star (repMatrix ρ (u (colLink Q)) a f) := rfl

/-- The frozen factor at `σ = false`, unfolded. -/
private theorem colFrozenFac_false (u u' : LayerLink N → G)
    (Q : LayerColumn N) (a b e f : Fin d) :
    colFrozenFac ρ u u' Q false a b e f
      = repMatrix ρ (u (colLink Q)) a b
        * star (repMatrix ρ (u' (colLink Q)) f e) := rfl

/-- At the base site, the site factor is the base factor. -/
theorem colSiteFac_base (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d)
    (g : G) :
    colSiteFac ρ Q σ a b e f Q.1 g = colBaseFac ρ Q σ a b e f g := by
  simp [colSiteFac]

/-- At the head site, the site factor is the head factor
(the head differs from the base at even `N`). -/
theorem colSiteFac_head (hN : Even N) (Q : LayerColumn N) (σ : Bool)
    (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q σ a b e f (colHead Q) g
      = colHeadFac ρ Q σ a b e f g := by
  have hne : colHead Q ≠ Q.1 := layerShift_ne_self hN Q.2.1 Q.2.2 Q.1
  simp [colSiteFac, hne]

/-- At a site the column does not read, the site factor
is `1`. -/
theorem colSiteFac_of_not_mem (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d)
    {r : LayerSite N} (hr : r ∉ colSites Q) (g : G) :
    colSiteFac ρ Q σ a b e f r g = 1 := by
  rw [colSites_eq] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  simp [colSiteFac, hr.1, hr.2]

/-- Table cell: plain column at its base — a plain entry. -/
theorem colSiteFac_base_plain (Q : LayerColumn N) (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q true a b e f Q.1 g = repMatrix ρ g a b := by
  rw [colSiteFac_base]; rfl

/-- Table cell: conjugated column at its base — a
conjugated entry. -/
theorem colSiteFac_base_conj (Q : LayerColumn N) (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q false a b e f Q.1 g = star (repMatrix ρ g a f) := by
  rw [colSiteFac_base]; rfl

/-- Table cell: plain column at its head — a conjugated
entry. -/
theorem colSiteFac_head_plain (hN : Even N) (Q : LayerColumn N)
    (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q true a b e f (colHead Q) g
      = star (repMatrix ρ g f e) := by
  rw [colSiteFac_head ρ hN]; rfl

/-- Table cell: conjugated column at its head — a plain
entry. -/
theorem colSiteFac_head_conj (hN : Even N) (Q : LayerColumn N)
    (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q false a b e f (colHead Q) g = repMatrix ρ g b e := by
  rw [colSiteFac_head ρ hN]; rfl

/-! ### §5b.1. The entry expansions

The trace of a four-fold matrix product as a four-fold
entry sum, and the two expansions of a column character —
plain and conjugated — into site factors times the frozen
factor. -/

/-- The trace of a four-fold product is the four-fold entry
sum, indices chained `a → b → e → f → a`. -/
private theorem trace_mul4 (A B C D : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (A * B * C * D)
      = ∑ a, ∑ b, ∑ e, ∑ f, A a b * B b e * C e f * D f a := by
  have h2 : ∀ X Y : Matrix (Fin d) (Fin d) ℂ,
      Matrix.trace (X * Y) = ∑ a, ∑ e, X a e * Y e a := by
    intro X Y
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Matrix.mul_assoc (A * B) C D, h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun e₀ _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun f _ => by ring

/-- **Entry expansion, plain column.** The character of a
column word is the sum over entry indices of its base
factor, head factor, and frozen factor, all at `σ = true`. -/
theorem charFn_colWord_expand (u u' : LayerLink N → G) (Q : LayerColumn N)
    (α : LayerSite N → G) :
    charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
      = ∑ a, ∑ b, ∑ e, ∑ f, colBaseFac ρ Q true a b e f (α Q.1)
          * colHeadFac ρ Q true a b e f (α (colHead Q))
          * colFrozenFac ρ u u' Q true a b e f := by
  have hword : repMatrix ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
      = repMatrix ρ (α Q.1) * repMatrix ρ (u' (colLink Q))
        * star (repMatrix ρ (α (colHead Q)))
        * star (repMatrix ρ (u (colLink Q))) := by
    show repMatrix ρ (α Q.1 * u' (colLink Q) * (α (colHead Q))⁻¹
      * (u (colLink Q))⁻¹) = _
    rw [repMatrix_mul, repMatrix_mul, repMatrix_mul, repMatrix_inv,
      repMatrix_inv]
  show Matrix.trace _ = _
  rw [hword, trace_mul4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  simp only [Matrix.star_apply, colBaseFac_true, colHeadFac_true,
    colFrozenFac_true]
  ring

/-- **Entry expansion, conjugated column.** The conjugate
of a column character is the character of the inverse word;
its expansion has the same shape at `σ = false`. -/
theorem star_charFn_colWord_expand (u u' : LayerLink N → G)
    (Q : LayerColumn N) (α : LayerSite N → G) :
    star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
      = ∑ a, ∑ b, ∑ e, ∑ f, colBaseFac ρ Q false a b e f (α Q.1)
          * colHeadFac ρ Q false a b e f (α (colHead Q))
          * colFrozenFac ρ u u' Q false a b e f := by
  have hstar : charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)⁻¹
      = star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)) := by
    rw [charFn_inv, starRingEnd_apply]
  have hinv : (colWord u u' Q.1 Q.2.1 Q.2.2 α)⁻¹
      = u (colLink Q) * α (colHead Q) * (u' (colLink Q))⁻¹ * (α Q.1)⁻¹ := by
    show (α Q.1 * u' (colLink Q) * (α (colHead Q))⁻¹ * (u (colLink Q))⁻¹)⁻¹
      = _
    group
  rw [← hstar, hinv]
  show Matrix.trace (repMatrix ρ (u (colLink Q) * α (colHead Q)
    * (u' (colLink Q))⁻¹ * (α Q.1)⁻¹)) = _
  rw [repMatrix_mul, repMatrix_mul, repMatrix_mul, repMatrix_inv,
    repMatrix_inv, trace_mul4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  simp only [Matrix.star_apply, colBaseFac_false, colHeadFac_false,
    colFrozenFac_false]
  ring

/-! ### §5b.2. R1: support factorization

The stratum integrand of `quadCharMoment`, on the ordered
columns of a primitive quad, is a product over the four
columns of plain/conjugated characters; each character
expands into entry sums; the integral of the expanded
product is a finite sum of products of single-site pair
integrals. -/

/-- The pointwise product identity: on the cycle ordering,
the `t`-split product of plain and conjugated characters
is the product over the four ordered columns of the
pattern-selected character. -/
private theorem quadCharIntegrand_eq_prod_ordered
    {C : Finset (LayerColumn N)} {s : Fin 4 → LayerSite N}
    {P : Fin 4 → LayerColumn N} (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    {t : Finset (LayerColumn N)} (ht : t ⊆ C) (u u' : LayerLink N → G)
    (α : LayerSite N → G) :
    (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
      * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
    = ∏ i : Fin 4, (if P i ∈ t
        then charFn ρ (colWord u u' (P i).1 (P i).2.1 (P i).2.2 α)
        else star (charFn ρ (colWord u u' (P i).1 (P i).2.1 (P i).2.2 α))) := by
  classical
  set F : LayerColumn N → ℂ := fun Q => if Q ∈ t
    then charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
    else star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)) with hF
  have himage : Finset.univ.image P = C := by
    apply Finset.Subset.antisymm
    · intro Q hQ
      rw [Finset.mem_image] at hQ
      obtain ⟨i, _, hi⟩ := hQ
      rw [← hi]; exact hPmem i
    · intro Q hQ
      obtain ⟨i, hi⟩ := hPcover Q hQ
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ i, hi⟩
  have hprodC : ∏ i : Fin 4, F (P i) = ∏ Q ∈ C, F Q := by
    rw [← himage, Finset.prod_image (fun i _ j _ h => hP h)]
  have hsplit : ∏ Q ∈ C, F Q
      = (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
        * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))) := by
    have ht' : ∏ Q ∈ t, F Q
        = ∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α) :=
      Finset.prod_congr rfl fun Q hQ => if_pos hQ
    have hc' : ∏ Q ∈ C \ t, F Q
        = ∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)) :=
      Finset.prod_congr rfl fun Q hQ => if_neg (Finset.mem_sdiff.mp hQ).2
    rw [← Finset.prod_sdiff ht, ht', hc']
    exact mul_comm _ _
  rw [hsplit] at hprodC
  exact hprodC.symm.trans (Finset.prod_congr rfl fun i _ => rfl)

/-- The pattern-selected character of one column, expanded:
the bridge between the `t`-membership form and the
Bool-indexed site factors. -/
private theorem colCharFac_expand (u u' : LayerLink N → G)
    (Q : LayerColumn N) (t : Finset (LayerColumn N))
    (α : LayerSite N → G) :
    (if Q ∈ t then charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)
      else star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
    = ∑ a, ∑ b, ∑ e, ∑ f, colBaseFac ρ Q (decide (Q ∈ t)) a b e f (α Q.1)
        * colHeadFac ρ Q (decide (Q ∈ t)) a b e f (α (colHead Q))
        * colFrozenFac ρ u u' Q (decide (Q ∈ t)) a b e f := by
  classical
  by_cases h : Q ∈ t
  · rw [if_pos h, show decide (Q ∈ t) = true by simp [h]]
    exact charFn_colWord_expand ρ u u' Q α
  · rw [if_neg h, show decide (Q ∈ t) = false by simp [h]]
    exact star_charFn_colWord_expand ρ u u' Q α

/-- Base factors are entries of a unitary matrix, or their
conjugates: norm at most `1`. -/
private theorem norm_colBaseFac_le (Q : LayerColumn N) (σ : Bool)
    (a b e f : Fin d) (g : G) : ‖colBaseFac ρ Q σ a b e f g‖ ≤ 1 := by
  cases σ with
  | true =>
    rw [colBaseFac_true]
    exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ g) a b
  | false =>
    rw [colBaseFac_false, norm_star]
    exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ g) a f

/-- Head factors have norm at most `1`. -/
private theorem norm_colHeadFac_le (Q : LayerColumn N) (σ : Bool)
    (a b e f : Fin d) (g : G) : ‖colHeadFac ρ Q σ a b e f g‖ ≤ 1 := by
  cases σ with
  | true =>
    rw [colHeadFac_true, norm_star]
    exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ g) f e
  | false =>
    rw [colHeadFac_false]
    exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ g) b e

/-- Frozen factors have norm at most `1`: a product of two
unitary entries (or conjugates). -/
private theorem norm_colFrozenFac_le (u u' : LayerLink N → G)
    (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d) :
    ‖colFrozenFac ρ u u' Q σ a b e f‖ ≤ 1 := by
  cases σ with
  | true =>
    rw [colFrozenFac_true]
    refine le_trans (norm_mul_le _ _) ?_
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) b e
    · rw [norm_star]
      exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) a f
  | false =>
    rw [colFrozenFac_false]
    refine le_trans (norm_mul_le _ _) ?_
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) a b
    · rw [norm_star]
      exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) f e

/-- Measurability of a base factor as a function of the
configuration, read at a site `r`. -/
private theorem measurable_colBaseFac_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d) (r : LayerSite N) :
    Measurable (fun α : LayerSite N → G =>
      colBaseFac ρ Q σ a b e f (α r)) := by
  have hentry : ∀ i j : Fin d, Measurable (fun α : LayerSite N → G =>
      repMatrix ρ (α r) i j) :=
    fun i j => (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (hρcont.measurable.comp
        (measurable_pi_apply r)))
  cases σ with
  | true =>
    have hfun : (fun α : LayerSite N → G =>
        colBaseFac ρ Q true a b e f (α r))
        = fun α : LayerSite N → G => repMatrix ρ (α r) a b :=
      funext fun α => colBaseFac_true ρ Q a b e f (α r)
    rw [hfun]
    exact hentry a b
  | false =>
    have hfun : (fun α : LayerSite N → G =>
        colBaseFac ρ Q false a b e f (α r))
        = fun α : LayerSite N → G => star (repMatrix ρ (α r) a f) :=
      funext fun α => colBaseFac_false ρ Q a b e f (α r)
    rw [hfun]
    exact continuous_star.measurable.comp (hentry a f)

/-- Finite `Fin 4` arithmetic facts used by the site
bookkeeping, all decidable. -/
private theorem fin4_facts : ∀ j : Fin 4, j ≠ j + 1 ∧ j ≠ j + 1 + 1
    ∧ j ≠ j + 2 ∧ j ≠ j + 2 + 1 ∧ j ≠ j + 3 ∧ j + 3 ≠ j
    ∧ (j + 3) + 1 = j := by decide

/-- **Regrouping**: the product over the columns of
(base factor · head factor) is the product over all sites
of the product of the site factors — each column
contributes at exactly its two sites. -/
private theorem prod_baseHeadFac_eq_prod_siteFac (hN : Even N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool) (a b e f : Fin 4 → Fin d)
    (α : LayerSite N → G) :
    ∏ i, (colBaseFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (α (P i).1)
        * colHeadFac ρ (P i) (σ i) (a i) (b i) (e i) (f i)
            (α (colHead (P i))))
    = ∏ r : LayerSite N, ∏ i, colSiteFac ρ (P i) (σ i) (a i) (b i) (e i)
        (f i) r (α r) := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hsupp : ∀ r : LayerSite N, r ∉ {(P i).1, colHead (P i)} →
      colSiteFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) r (α r) = 1 :=
    fun r hr => colSiteFac_of_not_mem ρ (P i) (σ i) (a i) (b i) (e i) (f i)
      (by rwa [colSites_eq]) (α r)
  have hne : (P i).1 ≠ colHead (P i) :=
    Ne.symm (layerShift_ne_self hN (P i).2.1 (P i).2.2 (P i).1)
  rw [← Finset.prod_subset (Finset.subset_univ {(P i).1, colHead (P i)})
    (fun r _ hr => hsupp r hr), Finset.prod_pair hne, colSiteFac_base,
    colSiteFac_head ρ hN]

/-- **Site collapse**: at the ordered site `s j`, only the
two incident columns `P (j + 3)` and `P j` contribute a
nontrivial site factor. -/
private theorem prod_colSiteFac_eq_pair
    (s : Fin 4 → LayerSite N) (P : Fin 4 → LayerColumn N)
    (hs : Function.Injective s)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)})
    (σ : Fin 4 → Bool) (a b e f : Fin 4 → Fin d) (j : Fin 4) (g : G) :
    ∏ i, colSiteFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (s j) g
    = colSiteFac ρ (P (j + 3)) (σ (j + 3)) (a (j + 3)) (b (j + 3))
        (e (j + 3)) (f (j + 3)) (s j) g
      * colSiteFac ρ (P j) (σ j) (a j) (b j) (e j) (f j) (s j) g := by
  have h1 : ∀ i : Fin 4, i ∉ ({j + 3, j} : Finset (Fin 4)) →
      colSiteFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (s j) g = 1 := by
    intro i hi
    have hcases : i = j + 1 ∨ i = j + 2 := by
      have hex : ∀ x y : Fin 4, x ∉ ({y + 3, y} : Finset (Fin 4)) →
          x = y + 1 ∨ x = y + 2 := by decide
      exact hex i j hi
    apply colSiteFac_of_not_mem
    rcases hcases with rfl | rfl
    · rw [hinc (j + 1)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hs.ne (fin4_facts j).1, hs.ne (fin4_facts j).2.1⟩
    · rw [hinc (j + 2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hs.ne (fin4_facts j).2.2.1, hs.ne (fin4_facts j).2.2.2.1⟩
  rw [← Finset.prod_subset (Finset.subset_univ ({j + 3, j} : Finset (Fin 4)))
    (fun i _ hi => h1 i hi), Finset.prod_pair (fin4_facts j).2.2.2.2.2.1]

/-- **Support collapse**: in the product over all sites of
the site integrals, every site outside the quad's support
contributes `1`, and the support is the image of the
ordered sites. -/
private theorem prod_siteIntFull_eq_ordered
    {C : Finset (LayerColumn N)} (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (hs : Function.Injective s)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)})
    (σ : Fin 4 → Bool) (a b e f : Fin 4 → Fin d) :
    (∏ r : LayerSite N, ∫ g, ∏ i, colSiteFac ρ (P i) (σ i) (a i) (b i)
        (e i) (f i) r g ∂μG)
    = ∏ j : Fin 4, ∫ g, ∏ i, colSiteFac ρ (P i) (σ i) (a i) (b i) (e i)
        (f i) (s j) g ∂μG := by
  have hsupp : quadSupport C = Finset.univ.image s := by
    ext r
    simp only [quadSupport, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨Q, hQC, hrQ⟩
      obtain ⟨i, hi⟩ := hPcover Q hQC
      rw [← hi, hinc i] at hrQ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrQ
      rcases hrQ with rfl | rfl
      · exact ⟨i, rfl⟩
      · exact ⟨i + 1, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨P j, hPmem j, by
        rw [hinc j]; exact Finset.mem_insert_self _ _⟩
  have hone : ∀ r : LayerSite N, r ∉ quadSupport C →
      (∫ g, ∏ i, colSiteFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) r g
        ∂μG) = 1 := by
    intro r hr
    have hfac : ∀ i, ∀ g : G,
        colSiteFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) r g = 1 :=
      fun i g => colSiteFac_of_not_mem ρ (P i) (σ i) (a i) (b i) (e i)
        (f i) (fun hmem => hr (Finset.mem_biUnion.mpr ⟨P i, hPmem i, hmem⟩)) g
    rw [integral_congr_ae (Filter.Eventually.of_forall fun g =>
      Finset.prod_eq_one (fun i _ => hfac i g))]
    simp
  rw [← Finset.prod_subset (Finset.subset_univ (quadSupport C))
    (fun r _ hr => hone r hr), hsupp,
    Finset.prod_image (fun i _ j _ h => hs h)]

/-- Measurability of a head factor as a function of the
configuration, read at a site `r`. -/
private theorem measurable_colHeadFac_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (Q : LayerColumn N) (σ : Bool) (a b e f : Fin d) (r : LayerSite N) :
    Measurable (fun α : LayerSite N → G =>
      colHeadFac ρ Q σ a b e f (α r)) := by
  have hentry : ∀ i j : Fin d, Measurable (fun α : LayerSite N → G =>
      repMatrix ρ (α r) i j) :=
    fun i j => (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (hρcont.measurable.comp
        (measurable_pi_apply r)))
  cases σ with
  | true =>
    have hfun : (fun α : LayerSite N → G =>
        colHeadFac ρ Q true a b e f (α r))
        = fun α : LayerSite N → G => star (repMatrix ρ (α r) f e) :=
      funext fun α => colHeadFac_true ρ Q a b e f (α r)
    rw [hfun]
    exact continuous_star.measurable.comp (hentry f e)
  | false =>
    have hfun : (fun α : LayerSite N → G =>
        colHeadFac ρ Q false a b e f (α r))
        = fun α : LayerSite N → G => repMatrix ρ (α r) b e :=
      funext fun α => colHeadFac_false ρ Q a b e f (α r)
    rw [hfun]
    exact hentry b e

/-- The integrability of one fully-indexed summand of the
expanded integrand: a product of site factors and frozen
factors, all of norm at most `1`. -/
private theorem integrable_ordered_summand
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool)
    (a b e f : Fin 4 → Fin d) :
    Integrable (fun α : LayerSite N → G => ∏ i,
        (colBaseFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (α (P i).1)
          * colHeadFac ρ (P i) (σ i) (a i) (b i) (e i) (f i)
              (α (colHead (P i)))
          * colFrozenFac ρ u u' (P i) (σ i) (a i) (b i) (e i) (f i)))
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun α => ?_)
  · exact (Finset.measurable_prod _ fun i _ =>
      ((measurable_colBaseFac_apply ρ hρcont (P i) (σ i) (a i) (b i)
          (e i) (f i) (P i).1).mul
        (measurable_colHeadFac_apply ρ hρcont (P i) (σ i) (a i) (b i)
          (e i) (f i) (colHead (P i)))).mul
        measurable_const).aestronglyMeasurable
  · refine le_trans (Finset.norm_prod_le _ _) ?_
    have hfac : ∀ i : Fin 4,
        ‖colBaseFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (α (P i).1)
          * colHeadFac ρ (P i) (σ i) (a i) (b i) (e i) (f i)
              (α (colHead (P i)))
          * colFrozenFac ρ u u' (P i) (σ i) (a i) (b i) (e i) (f i)‖
          ≤ 1 := by
      intro i
      have hb := norm_colBaseFac_le ρ (P i) (σ i) (a i) (b i) (e i) (f i)
        (α (P i).1)
      have hh := norm_colHeadFac_le ρ (P i) (σ i) (a i) (b i) (e i) (f i)
        (α (colHead (P i)))
      have hf := norm_colFrozenFac_le ρ u u' (P i) (σ i) (a i) (b i) (e i)
        (f i)
      calc ‖colBaseFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (α (P i).1)
            * colHeadFac ρ (P i) (σ i) (a i) (b i) (e i) (f i)
                (α (colHead (P i)))
            * colFrozenFac ρ u u' (P i) (σ i) (a i) (b i) (e i) (f i)‖
          ≤ ‖colBaseFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (α (P i).1)‖
            * ‖colHeadFac ρ (P i) (σ i) (a i) (b i) (e i) (f i)
                (α (colHead (P i)))‖
            * ‖colFrozenFac ρ u u' (P i) (σ i) (a i) (b i) (e i) (f i)‖ := by
            refine le_trans (norm_mul_le _ _) ?_
            exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul hb hh (norm_nonneg _) (by norm_num)) hf
              (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    rw [Fin.prod_univ_four]
    refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul (hfac 0) (hfac 1)
      (norm_nonneg _) (by norm_num)) (hfac 2) (norm_nonneg _) (by norm_num))
      (hfac 3) (norm_nonneg _) (by norm_num)) (by norm_num)

/-- **R1 — support factorization.** The character moment
of a primitive quad, read along the cyclic ordering
`P` of its columns over the ordered sites `s`, is the
entry expansion of the frozen factors times the product
over the four ordered sites of the two-factor site
integrals. Every non-support site has integrated to `1`
against the product measure; the remaining sewing is
exactly the per-site pair of column factors. This is the
form the assembly consumes. -/
theorem quadCharMoment_eq_sum_siteInt (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {C : Finset (LayerColumn N)} {s : Fin 4 → LayerSite N}
    {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)})
    {t : Finset (LayerColumn N)} (ht : t ⊆ C) (u u' : LayerLink N → G) :
    quadCharMoment ρ μG C t u u'
    = ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
      ∑ f : Fin 4 → Fin d,
        (∏ i, colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i)
            (e i) (f i))
        * ∏ j : Fin 4, ∫ g,
            (colSiteFac ρ (P (j + 3)) (decide (P (j + 3) ∈ t))
                (a (j + 3)) (b (j + 3)) (e (j + 3)) (f (j + 3)) (s j) g
              * colSiteFac ρ (P j) (decide (P j ∈ t)) (a j) (b j) (e j)
                (f j) (s j) g) ∂μG := by
  classical
  have hswap : ∀ α : LayerSite N → G,
      (∏ i, ∑ a : Fin d, ∑ b : Fin d, ∑ e : Fin d, ∑ f : Fin d,
        colBaseFac ρ (P i) (decide (P i ∈ t)) a b e f (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) a b e f (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) a b e f)
      = ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
        ∑ f : Fin 4 → Fin d, ∏ i,
          colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
            (α (P i).1)
          * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
            (α (colHead (P i)))
          * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
            (f i) := by
    intro α
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Fintype.prod_sum]
  have hInt : ∀ (a b e f : Fin 4 → Fin d), Integrable
      (fun α : LayerSite N → G => ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i))
      (Measure.pi fun _ : LayerSite N => μG) :=
    fun a b e f => integrable_ordered_summand ρ μG hρcont u u' P
      (fun i => decide (P i ∈ t)) a b e f
  have hpt : ∀ α : LayerSite N → G,
      (∏ Q ∈ t, charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α))
        * (∏ Q ∈ C \ t, star (charFn ρ (colWord u u' Q.1 Q.2.1 Q.2.2 α)))
      = ∏ i, (∑ a : Fin d, ∑ b : Fin d, ∑ e : Fin d, ∑ f : Fin d,
        colBaseFac ρ (P i) (decide (P i ∈ t)) a b e f (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) a b e f (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) a b e f) := by
    intro α
    rw [quadCharIntegrand_eq_prod_ordered (s := s) ρ hP hPmem hPcover ht u u' α]
    exact Finset.prod_congr rfl fun i _ => colCharFac_expand ρ u u' (P i) t α
  unfold quadCharMoment
  trans ∫ α, ∏ i, (∑ a : Fin d, ∑ b : Fin d, ∑ e : Fin d, ∑ f : Fin d,
      colBaseFac ρ (P i) (decide (P i ∈ t)) a b e f (α (P i).1)
      * colHeadFac ρ (P i) (decide (P i ∈ t)) a b e f (α (colHead (P i)))
      * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) a b e f)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  trans ∫ α, ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d,
      ∑ e : Fin 4 → Fin d, ∑ f : Fin 4 → Fin d, ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · exact integral_congr_ae (Filter.Eventually.of_forall fun α => hswap α)
  trans ∑ a : Fin 4 → Fin d, ∫ α, ∑ b : Fin 4 → Fin d,
      ∑ e : Fin 4 → Fin d, ∑ f : Fin 4 → Fin d, ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · exact integral_finset_sum _ (fun a _ => integrable_finset_sum _
      (fun b _ => integrable_finset_sum _ (fun e _ =>
        integrable_finset_sum _ (fun f _ => hInt a b e f))))
  trans ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d, ∫ α,
      ∑ e : Fin 4 → Fin d, ∑ f : Fin 4 → Fin d, ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · refine Finset.sum_congr rfl fun a _ => integral_finset_sum _
      (fun b _ => integrable_finset_sum _ (fun e _ =>
        integrable_finset_sum _ (fun f _ => hInt a b e f)))
  trans ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
      ∫ α, ∑ f : Fin 4 → Fin d, ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      integral_finset_sum _ (fun e _ => integrable_finset_sum _
        (fun f _ => hInt a b e f))
  trans ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
      ∑ f : Fin 4 → Fin d, ∫ α, ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => integral_finset_sum _
        (fun f _ => hInt a b e f)
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  have hstep : ∫ α, ∏ i,
        colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (P i).1)
        * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
          (α (colHead (P i)))
        * colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
          (f i)
      ∂(Measure.pi fun _ : LayerSite N => μG)
      = (∏ i, colFrozenFac ρ u u' (P i) (decide (P i ∈ t)) (a i) (b i)
          (e i) (f i))
        * ∫ α, ∏ i,
            colBaseFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i)
              (α (P i).1)
            * colHeadFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i)
              (f i) (α (colHead (P i)))
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)).trans
      (integral_const_mul _ _)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hstep]
  refine congrArg (fun z => (∏ i, colFrozenFac ρ u u' (P i)
    (decide (P i ∈ t)) (a i) (b i) (e i) (f i)) * z) ?_
  trans ∫ α, ∏ r : LayerSite N, ∏ i, colSiteFac ρ (P i)
      (decide (P i ∈ t)) (a i) (b i) (e i) (f i) r (α r)
    ∂(Measure.pi fun _ : LayerSite N => μG)
  · exact integral_congr_ae (Filter.Eventually.of_forall fun α =>
      prod_baseHeadFac_eq_prod_siteFac ρ hN P (fun i => decide (P i ∈ t))
        a b e f α)
  trans ∏ r : LayerSite N, ∫ g, ∏ i, colSiteFac ρ (P i)
      (decide (P i ∈ t)) (a i) (b i) (e i) (f i) r g ∂μG
  · exact integral_fintype_prod_eq_prod (fun r g => ∏ i,
      colSiteFac ρ (P i) (decide (P i ∈ t)) (a i) (b i) (e i) (f i) r g)
  trans ∏ j : Fin 4, ∫ g, ∏ i, colSiteFac ρ (P i) (decide (P i ∈ t))
      (a i) (b i) (e i) (f i) (s j) g ∂μG
  · exact prod_siteIntFull_eq_ordered ρ μG s P hs hPmem hPcover hinc
      (fun i => decide (P i ∈ t)) a b e f
  · exact Finset.prod_congr rfl fun j _ => integral_congr_ae
      (Filter.Eventually.of_forall fun g =>
        prod_colSiteFac_eq_pair ρ s P hs hinc (fun i => decide (P i ∈ t))
          a b e f j g)

end ContractionEngine

/-! ## 5b.3 — The per-site type table

At each ordered site `s j` exactly two columns are incident,
`P (j + 3)` and `P j`. The `siteSplit` at the site counts
the incident columns based there; this section turns the
split value and the two pattern signs into the concrete
entry (a plain `repMatrix` entry or its conjugate) that
each site factor reduces to. All four entry evaluations are
already owned: the mixed pair in both orientations by
`RepOrthogonality`, the same-orientation pairs by
`RepTensorTwirl`. The pair at a site is then: mixed exactly
when the two reduced entries have opposite star-status,
a `(2, 0)` pair when both are plain, a `(0, 2)` pair when
both are conjugated — the grammar of the scoping's table,
with the evaluations owned by `RepOrthogonality` (mixed)
and `RepTensorTwirl` (same-orientation). -/

section SiteTypeTable

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The degree at an ordered site of an enumerated quad
is exactly `2`: the incident columns are `P (j + 3)` and
`P j` and no others. -/
private theorem siteDegree_ordered_site {C : Finset (LayerColumn N)}
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)}) (j : Fin 4) :
    siteDegree C (s j) = 2 := by
  have hmem1 : s j ∈ colSites (P (j + 3)) := by
    rw [hinc (j + 3), show j + 3 + 1 = j from (fin4_facts j).2.2.2.2.2.2]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem2 : s j ∈ colSites (P j) := by
    rw [hinc j]
    exact Finset.mem_insert_self _ _
  have hfilter : C.filter (fun Q => s j ∈ colSites Q) = {P (j + 3), P j} := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hRC, hR⟩
      obtain ⟨i, rfl⟩ := hPcover R hRC
      rw [hinc i] at hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with h | h
      · exact Or.inr (congrArg P (hs h).symm)
      · have hpre : ∀ x y : Fin 4, x = y + 1 → y = x + 3 := by decide
        exact Or.inl (congrArg P (hpre j i (hs h)))
    · rintro (rfl | rfl)
      · exact ⟨hPmem _, hmem1⟩
      · exact ⟨hPmem _, hmem2⟩
  unfold siteDegree
  rw [hfilter, Finset.card_pair]
  exact hP.ne (fin4_facts j).2.2.2.2.2.1

/-- The first component of the split at an ordered site,
as the sum of the two based-indicators of the incident
columns. -/
theorem siteSplit_fst_ordered {C : Finset (LayerColumn N)}
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)}) (j : Fin 4) :
    (siteSplit C (s j)).1
      = (if (P (j + 3)).1 = s j then 1 else 0)
        + (if (P j).1 = s j then 1 else 0) := by
  have hdeg := siteDegree_ordered_site hs hP hPmem hPcover hinc j
  have hmem1 : s j ∈ colSites (P (j + 3)) := by
    rw [hinc (j + 3), show j + 3 + 1 = j from (fin4_facts j).2.2.2.2.2.2]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem2 : s j ∈ colSites (P j) := by
    rw [hinc j]
    exact Finset.mem_insert_self _ _
  have hAB : P (j + 3) ≠ P j := hP.ne (fin4_facts j).2.2.2.2.2.1
  have hpair := incident_pair_of_degree_two hdeg (hPmem (j + 3)) hmem1
    (hPmem j) hmem2 hAB
  exact siteSplit_fst_of_incident_pair hdeg hAB hpair (hPmem (j + 3))
    (hPmem j)

/-- **Table row, source**: split first component `2` at an
ordered site — both incident columns are based there. -/
theorem based_pair_of_split_two {C : Finset (LayerColumn N)}
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)}) (j : Fin 4)
    (h2 : (siteSplit C (s j)).1 = 2) :
    (P (j + 3)).1 = s j ∧ (P j).1 = s j := by
  rw [siteSplit_fst_ordered hs hP hPmem hPcover hinc j] at h2
  by_cases ha : (P (j + 3)).1 = s j <;> by_cases hb : (P j).1 = s j
  · exact ⟨ha, hb⟩
  · rw [if_pos ha, if_neg hb] at h2; omega
  · rw [if_neg ha, if_pos hb] at h2; omega
  · rw [if_neg ha, if_neg hb] at h2; omega

/-- **Table row, sink**: split first component `0` at an
ordered site — neither incident column is based there;
both are headed there. -/
theorem based_none_of_split_zero {C : Finset (LayerColumn N)}
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)}) (j : Fin 4)
    (h0 : (siteSplit C (s j)).1 = 0) :
    (P (j + 3)).1 ≠ s j ∧ (P j).1 ≠ s j := by
  rw [siteSplit_fst_ordered hs hP hPmem hPcover hinc j] at h0
  by_cases ha : (P (j + 3)).1 = s j <;> by_cases hb : (P j).1 = s j
  · rw [if_pos ha, if_pos hb] at h0; omega
  · rw [if_pos ha, if_neg hb] at h0; omega
  · rw [if_neg ha, if_pos hb] at h0; omega
  · exact ⟨ha, hb⟩

/-- **Table row, flank**: split first component `1` at an
ordered site — exactly one incident column is based
there, the other headed. -/
theorem based_xor_of_split_one {C : Finset (LayerColumn N)}
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)}) (j : Fin 4)
    (h1 : (siteSplit C (s j)).1 = 1) :
    ((P (j + 3)).1 = s j ∧ (P j).1 ≠ s j)
      ∨ ((P (j + 3)).1 ≠ s j ∧ (P j).1 = s j) := by
  rw [siteSplit_fst_ordered hs hP hPmem hPcover hinc j] at h1
  by_cases ha : (P (j + 3)).1 = s j <;> by_cases hb : (P j).1 = s j
  · rw [if_pos ha, if_pos hb] at h1; omega
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · rw [if_neg ha, if_neg hb] at h1; omega

/-- The entry a site factor reduces to at its column's
base: a plain entry at sign `true`, a conjugated entry at
sign `false`. -/
theorem colSiteFac_base_entry (Q : LayerColumn N) (σ : Bool)
    (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q σ a b e f Q.1 g
      = if σ then repMatrix ρ g a b else star (repMatrix ρ g a f) := by
  cases σ with
  | true => rw [if_pos rfl]; exact colSiteFac_base_plain ρ Q a b e f g
  | false => rw [if_neg (by decide)]; exact colSiteFac_base_conj ρ Q a b e f g

/-- The entry a site factor reduces to at its column's
head: a conjugated entry at sign `true`, a plain entry
at sign `false`. -/
theorem colSiteFac_head_entry (hN : Even N) (Q : LayerColumn N) (σ : Bool)
    (a b e f : Fin d) (g : G) :
    colSiteFac ρ Q σ a b e f (colHead Q) g
      = if σ then star (repMatrix ρ g f e) else repMatrix ρ g b e := by
  cases σ with
  | true => rw [if_pos rfl]; exact colSiteFac_head_plain ρ hN Q a b e f g
  | false => rw [if_neg (by decide)]; exact colSiteFac_head_conj ρ hN Q a b e f g

/-- The base entry reduction at an ordered site, for an
incident column based there. -/
theorem colSiteFac_ordered_of_base {P : Fin 4 → LayerColumn N}
    {s : Fin 4 → LayerSite N} (i j : Fin 4) (σ : Bool)
    (a b e f : Fin 4 → Fin d) (g : G) (h : (P i).1 = s j) :
    colSiteFac ρ (P i) σ (a i) (b i) (e i) (f i) (s j) g
      = if σ then repMatrix ρ g (a i) (b i)
        else star (repMatrix ρ g (a i) (f i)) := by
  rw [← h]
  exact colSiteFac_base_entry ρ (P i) σ (a i) (b i) (e i) (f i) g

/-- The head entry reduction at an ordered site, for an
incident column headed there. -/
theorem colSiteFac_ordered_of_head (hN : Even N)
    {P : Fin 4 → LayerColumn N} {s : Fin 4 → LayerSite N} (i j : Fin 4)
    (σ : Bool) (a b e f : Fin 4 → Fin d) (g : G)
    (hmem : s j ∈ colSites (P i)) (h : (P i).1 ≠ s j) :
    colSiteFac ρ (P i) σ (a i) (b i) (e i) (f i) (s j) g
      = if σ then star (repMatrix ρ g (f i) (e i))
        else repMatrix ρ g (b i) (e i) := by
  have hhead : colHead (P i) = s j := by
    have hmem' : s j ∈ ({(P i).1, colHead (P i)} : Finset (LayerSite N)) := by
      rwa [colSites_eq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h1 | h1
    · exact absurd h1.symm h
    · exact h1.symm
  rw [← hhead]
  exact colSiteFac_head_entry ρ hN (P i) σ (a i) (b i) (e i) (f i) g

end SiteTypeTable

/-! ## 5b.4 — R2: the twisted contraction

The entry-level sewing lemmas. Where `QuadReMomentTelescope`
sews two traces, the assembly sews two entries carrying
frozen sandwiches `A B C D`; the contraction at a mixed
site is the Peter–Weyl evaluation with the sandwiches
contracted crosswise, and at a same-orientation site it
is the `RepTensorTwirl` evaluation, whose `J`-insertion
lands inside the running sandwiches. The closure
identities at the end regroup the `charFn_sewing`
contraction as a Frobenius pairing against `J` and record
the squared-norm form of a self-paired entry sum. No sign
is asserted anywhere in this section: these are exact
evaluations of pair contractions. -/

section TwistedContraction

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- Entries of a triple matrix product, expanded. -/
private theorem mul3_apply (A B C : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * B * C) i j = ∑ p, ∑ q, A i p * B p q * C q j := by
  have h1 : (A * B * C) i j = ∑ q, ∑ p, A i p * B p q * C q j := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [h1, Finset.sum_comm]

/-- Integrability of a plain-times-plain entry product. -/
private theorem integrable_repMatrix_entry_mul
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j k l : Fin d) :
    Integrable (fun g => repMatrix ρ g i j * repMatrix ρ g k l) μG := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  exact matFn_integrable_entry_mul μG _ _ hMmul hMone hMinv hMcont
    hMmul hMone hMinv hMcont i j k l

/-- Integrability of a conjugate-times-conjugate entry
product. -/
private theorem integrable_repMatrix_entry_star_mul_star
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j k l : Fin d) :
    Integrable (fun g => star (repMatrix ρ g i j)
      * star (repMatrix ρ g k l)) μG := by
  obtain ⟨hNmul, hNone, hNinv, hNcont⟩ := repMatConj_isOrientationMat ρ hρcont
  have hInt : Integrable (fun g => repMatConj ρ g i j * repMatConj ρ g k l)
      μG := matFn_integrable_entry_mul μG _ _ hNmul hNone hNinv hNcont
    hNmul hNone hNinv hNcont i j k l
  refine hInt.congr (Filter.Eventually.of_forall fun g => ?_)
  show repMatConj ρ g i j * repMatConj ρ g k l
    = star (repMatrix ρ g i j) * star (repMatrix ρ g k l)
  rw [show repMatConj ρ g i j = star (repMatrix ρ g i j) from
    orientConj_apply _ _ _ _, show repMatConj ρ g k l
    = star (repMatrix ρ g k l) from orientConj_apply _ _ _ _]

/-- **R2, mixed site.** The entry-level sewing with frozen
sandwiches: contracting a plain entry against a conjugated
entry sews the sandwiches crosswise — the first factors
contract through the conjugate transpose, the second
through the transpose against the entrywise conjugate. -/
theorem integral_entry_sandwich_mul_star
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ)
    (A B C D : Matrix (Fin d) (Fin d) ℂ) (i j k l : Fin d) :
    ∫ g, (A * repMatrix ρ g * B) i j
        * star ((C * repMatrix ρ g * D) k l) ∂μG
      = (d : ℂ)⁻¹ * ((A * Cᴴ) i k
          * (Bᵀ * D.map (starRingEnd ℂ)) j l) := by
  classical
  have hexp : ∀ g : G, (A * repMatrix ρ g * B) i j
        * star ((C * repMatrix ρ g * D) k l)
      = ∑ p, ∑ q, ∑ r, ∑ s, (A i p * star (C k r)) * (B q j * star (D s l))
          * (repMatrix ρ g p q * star (repMatrix ρ g r s)) := by
    intro g
    have e2 : star ((C * repMatrix ρ g * D) k l)
        = ∑ r, ∑ s, star (D s l) * star (repMatrix ρ g r s)
            * star (C k r) := by
      rw [mul3_apply, star_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [star_mul, star_mul, mul_assoc]
    rw [mul3_apply, e2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hterm : ∀ p q r s : Fin d,
      (∫ g, (A i p * star (C k r)) * (B q j * star (D s l))
          * (repMatrix ρ g p q * star (repMatrix ρ g r s)) ∂μG)
        = (A i p * star (C k r)) * (B q j * star (D s l))
          * (if p = r ∧ q = s then (d : ℂ)⁻¹ else 0) := by
    intro p q r s
    rw [integral_const_mul,
      integral_repMatrix_mul_star_repMatrix μG ρ hρcont hρirr p q r s]
  have hswap : (∫ g, ∑ p, ∑ q, ∑ r, ∑ s, (A i p * star (C k r))
          * (B q j * star (D s l))
          * (repMatrix ρ g p q * star (repMatrix ρ g r s)) ∂μG)
      = ∑ p, ∑ q, ∑ r, ∑ s, ∫ g, (A i p * star (C k r))
          * (B q j * star (D s l))
          * (repMatrix ρ g p q * star (repMatrix ρ g r s)) ∂μG :=
    (MeasureTheory.integral_finsetSum Finset.univ
      (fun p _ => MeasureTheory.integrable_finsetSum Finset.univ
        (fun q _ => MeasureTheory.integrable_finsetSum Finset.univ
          (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun s _ => (integrable_repMatrix_entry_mul_star ρ μG hρcont
              p q r s).const_mul _))))).trans
      (Finset.sum_congr rfl fun p _ =>
        (MeasureTheory.integral_finsetSum Finset.univ
          (fun q _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
              (fun s _ => (integrable_repMatrix_entry_mul_star ρ μG hρcont
                p q r s).const_mul _)))).trans
          (Finset.sum_congr rfl fun q _ =>
            (MeasureTheory.integral_finsetSum Finset.univ
              (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
                (fun s _ => (integrable_repMatrix_entry_mul_star ρ μG
                  hρcont p q r s).const_mul _))).trans
              (Finset.sum_congr rfl fun r _ =>
                MeasureTheory.integral_finsetSum Finset.univ
                  (fun s _ => (integrable_repMatrix_entry_mul_star ρ μG
                    hρcont p q r s).const_mul _))))
  have hcol : ∀ p q : Fin d, (∑ r, ∑ s, (A i p * star (C k r))
          * (B q j * star (D s l))
          * (if p = r ∧ q = s then (d : ℂ)⁻¹ else 0))
      = (A i p * star (C k p)) * (B q j * star (D q l)) * (d : ℂ)⁻¹ := by
    intro p q
    have hs1 : (∑ s, (A i p * star (C k p)) * (B q j * star (D s l))
          * (if p = p ∧ q = s then (d : ℂ)⁻¹ else 0))
        = (A i p * star (C k p)) * (B q j * star (D q l)) * (d : ℂ)⁻¹ := by
      rw [Finset.sum_eq_single q (fun s _ hs => ?_)
        (fun hq => absurd (Finset.mem_univ q) hq)]
      · rw [if_pos ⟨rfl, rfl⟩]
      · rw [if_neg (fun h => hs h.2.symm), mul_zero]
    rw [Finset.sum_eq_single p (fun r _ hr => ?_)
      (fun hp => absurd (Finset.mem_univ p) hp)]
    · exact hs1
    · refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg (fun h => hr h.1.symm), mul_zero]
  have hid1 : (∑ p, A i p * star (C k p)) = (A * Cᴴ) i k := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hid2 : (∑ q, B q j * star (D q l))
      = (Bᵀ * D.map (starRingEnd ℂ)) j l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      starRingEnd_apply]
  have hfin : (∑ p, ∑ q, (A i p * star (C k p)) * (B q j * star (D q l))
        * (d : ℂ)⁻¹)
      = (d : ℂ)⁻¹ * ((A * Cᴴ) i k * (Bᵀ * D.map (starRingEnd ℂ)) j l) := by
    trans (d : ℂ)⁻¹ * ((∑ p, A i p * star (C k p))
        * (∑ q, B q j * star (D q l)))
    · rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    · rw [hid1, hid2]
  calc ∫ g, (A * repMatrix ρ g * B) i j
        * star ((C * repMatrix ρ g * D) k l) ∂μG
      = ∫ g, ∑ p, ∑ q, ∑ r, ∑ s, (A i p * star (C k r))
          * (B q j * star (D s l))
          * (repMatrix ρ g p q * star (repMatrix ρ g r s)) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hexp)
    _ = ∑ p, ∑ q, ∑ r, ∑ s, ∫ g, (A i p * star (C k r))
          * (B q j * star (D s l))
          * (repMatrix ρ g p q * star (repMatrix ρ g r s)) ∂μG := hswap
    _ = ∑ p, ∑ q, (A i p * star (C k p)) * (B q j * star (D q l))
          * (d : ℂ)⁻¹ :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
          (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
            hterm p q r s).trans (hcol p q)
    _ = (d : ℂ)⁻¹ * ((A * Cᴴ) i k * (Bᵀ * D.map (starRingEnd ℂ)) j l) :=
        hfin

/-- **R2, `(2, 0)` site.** The same-orientation sewing:
contracting two plain entries inserts the canonical form
`J` into the running sandwiches — its conjugate on the
first index pair, `J` itself on the second — and the whole
contraction vanishes when the Frobenius–Schur indicator
is `0`. -/
theorem integral_entry_sandwich_mul (hd : 0 < d)
    (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (A B C D : Matrix (Fin d) (Fin d) ℂ) (i j k l : Fin d) :
    ∫ g, (A * repMatrix ρ g * B) i j * (C * repMatrix ρ g * D) k l ∂μG
      = if fsIndicator ρ μG = 0 then 0
        else (d : ℂ)⁻¹ * ((A * (canonicalForm ρ).map (starRingEnd ℂ) * Cᵀ) i k
          * (Bᵀ * canonicalForm ρ * D) j l) := by
  classical
  have hexp : ∀ g : G, (A * repMatrix ρ g * B) i j
        * (C * repMatrix ρ g * D) k l
      = ∑ p, ∑ q, ∑ r, ∑ s, (A i p * C k r) * (B q j * D s l)
          * (repMatrix ρ g p q * repMatrix ρ g r s) := by
    intro g
    rw [mul3_apply, mul3_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hterm : ∀ p q r s : Fin d,
      (∫ g, (A i p * C k r) * (B q j * D s l)
          * (repMatrix ρ g p q * repMatrix ρ g r s) ∂μG)
        = (A i p * C k r) * (B q j * D s l)
          * (if fsIndicator ρ μG = 0 then 0
            else (d : ℂ)⁻¹ * (star ((canonicalForm ρ) p r)
              * (canonicalForm ρ) q s)) := by
    intro p q r s
    rw [integral_const_mul,
      integral_repMatrix_mul_repMatrix μG ρ hd hρirr hρcont p q r s]
  have hswap : (∫ g, ∑ p, ∑ q, ∑ r, ∑ s, (A i p * C k r) * (B q j * D s l)
          * (repMatrix ρ g p q * repMatrix ρ g r s) ∂μG)
      = ∑ p, ∑ q, ∑ r, ∑ s, ∫ g, (A i p * C k r) * (B q j * D s l)
          * (repMatrix ρ g p q * repMatrix ρ g r s) ∂μG :=
    (MeasureTheory.integral_finsetSum Finset.univ
      (fun p _ => MeasureTheory.integrable_finsetSum Finset.univ
        (fun q _ => MeasureTheory.integrable_finsetSum Finset.univ
          (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun s _ => (integrable_repMatrix_entry_mul ρ μG hρcont
              p q r s).const_mul _))))).trans
      (Finset.sum_congr rfl fun p _ =>
        (MeasureTheory.integral_finsetSum Finset.univ
          (fun q _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
              (fun s _ => (integrable_repMatrix_entry_mul ρ μG hρcont
                p q r s).const_mul _)))).trans
          (Finset.sum_congr rfl fun q _ =>
            (MeasureTheory.integral_finsetSum Finset.univ
              (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
                (fun s _ => (integrable_repMatrix_entry_mul ρ μG
                  hρcont p q r s).const_mul _))).trans
              (Finset.sum_congr rfl fun r _ =>
                MeasureTheory.integral_finsetSum Finset.univ
                  (fun s _ => (integrable_repMatrix_entry_mul ρ μG
                    hρcont p q r s).const_mul _))))
  have hid1 : (∑ p, ∑ r, A i p * star ((canonicalForm ρ) p r) * C k r)
      = (A * (canonicalForm ρ).map (starRingEnd ℂ) * Cᵀ) i k := by
    symm
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      starRingEnd_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hid2 : (∑ q, ∑ s, B q j * (canonicalForm ρ) q s * D s l)
      = (Bᵀ * canonicalForm ρ * D) j l := by
    symm
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsplit : (∑ p, ∑ q, ∑ r, ∑ s, (A i p * star ((canonicalForm ρ) p r)
          * C k r) * (B q j * (canonicalForm ρ) q s * D s l))
      = ((∑ p, ∑ r, A i p * star ((canonicalForm ρ) p r) * C k r))
        * (∑ q, ∑ s, B q j * (canonicalForm ρ) q s * D s l) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul_sum]
  by_cases hν : fsIndicator ρ μG = 0
  · rw [if_pos hν]
    calc ∫ g, (A * repMatrix ρ g * B) i j * (C * repMatrix ρ g * D) k l ∂μG
        = ∑ p, ∑ q, ∑ r, ∑ s, ∫ g, (A i p * C k r) * (B q j * D s l)
            * (repMatrix ρ g p q * repMatrix ρ g r s) ∂μG :=
          (integral_congr_ae (Filter.Eventually.of_forall hexp)).trans hswap
      _ = ∑ p, ∑ q, ∑ r, ∑ s, (0 : ℂ) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
            Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by
              rw [hterm p q r s, if_pos hν, mul_zero]
      _ = 0 := by simp only [Finset.sum_const_zero]
  · rw [if_neg hν]
    calc ∫ g, (A * repMatrix ρ g * B) i j * (C * repMatrix ρ g * D) k l ∂μG
        = ∑ p, ∑ q, ∑ r, ∑ s, (A i p * C k r) * (B q j * D s l)
            * ((d : ℂ)⁻¹ * (star ((canonicalForm ρ) p r)
              * (canonicalForm ρ) q s)) :=
          (integral_congr_ae (Filter.Eventually.of_forall hexp)).trans
            (hswap.trans (Finset.sum_congr rfl fun p _ =>
              Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl
                fun r _ => Finset.sum_congr rfl fun s _ =>
                  (hterm p q r s).trans (by rw [if_neg hν])))
      _ = (d : ℂ)⁻¹ * ((∑ p, ∑ r, A i p * star ((canonicalForm ρ) p r)
              * C k r)
            * (∑ q, ∑ s, B q j * (canonicalForm ρ) q s * D s l)) := by
          trans (d : ℂ)⁻¹ * (∑ p, ∑ q, ∑ r, ∑ s,
              (A i p * star ((canonicalForm ρ) p r) * C k r)
              * (B q j * (canonicalForm ρ) q s * D s l))
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
          · rw [hsplit]
      _ = (d : ℂ)⁻¹ * ((A * (canonicalForm ρ).map (starRingEnd ℂ) * Cᵀ) i k
            * (Bᵀ * canonicalForm ρ * D) j l) := by rw [hid1, hid2]

/-- **R2, `(0, 2)` site.** The conjugate same-orientation
sewing: two conjugated entries contract through `J` on
the first index pair and its conjugate on the second;
again the contraction vanishes at indicator `0`. -/
theorem integral_entry_sandwich_star_mul_star (hd : 0 < d)
    (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (A B C D : Matrix (Fin d) (Fin d) ℂ) (i j k l : Fin d) :
    ∫ g, star ((A * repMatrix ρ g * B) i j)
        * star ((C * repMatrix ρ g * D) k l) ∂μG
      = if fsIndicator ρ μG = 0 then 0
        else (d : ℂ)⁻¹ * (((A.map (starRingEnd ℂ)) * canonicalForm ρ * Cᴴ) i k
          * (Bᴴ * (canonicalForm ρ).map (starRingEnd ℂ)
            * D.map (starRingEnd ℂ)) j l) := by
  classical
  have hexp : ∀ g : G, star ((A * repMatrix ρ g * B) i j)
        * star ((C * repMatrix ρ g * D) k l)
      = ∑ p, ∑ q, ∑ r, ∑ s, (star (A i p) * star (C k r))
          * (star (B q j) * star (D s l))
          * (star (repMatrix ρ g p q) * star (repMatrix ρ g r s)) := by
    intro g
    have e1 : star ((A * repMatrix ρ g * B) i j)
        = ∑ p, ∑ q, star (B q j) * star (repMatrix ρ g p q) * star (A i p) := by
      rw [mul3_apply, star_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [star_mul, star_mul, mul_assoc]
    have e2 : star ((C * repMatrix ρ g * D) k l)
        = ∑ r, ∑ s, star (D s l) * star (repMatrix ρ g r s)
            * star (C k r) := by
      rw [mul3_apply, star_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [star_mul, star_mul, mul_assoc]
    rw [e1, e2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hterm : ∀ p q r s : Fin d,
      (∫ g, (star (A i p) * star (C k r)) * (star (B q j) * star (D s l))
          * (star (repMatrix ρ g p q) * star (repMatrix ρ g r s)) ∂μG)
        = (star (A i p) * star (C k r)) * (star (B q j) * star (D s l))
          * (if fsIndicator ρ μG = 0 then 0
            else (d : ℂ)⁻¹ * ((canonicalForm ρ) p r
              * star ((canonicalForm ρ) q s))) := by
    intro p q r s
    rw [integral_const_mul,
      integral_star_repMatrix_mul_star_repMatrix μG ρ hd hρirr hρcont
        p q r s]
  have hswap : (∫ g, ∑ p, ∑ q, ∑ r, ∑ s, (star (A i p) * star (C k r))
          * (star (B q j) * star (D s l))
          * (star (repMatrix ρ g p q) * star (repMatrix ρ g r s)) ∂μG)
      = ∑ p, ∑ q, ∑ r, ∑ s, ∫ g, (star (A i p) * star (C k r))
          * (star (B q j) * star (D s l))
          * (star (repMatrix ρ g p q) * star (repMatrix ρ g r s)) ∂μG :=
    (MeasureTheory.integral_finsetSum Finset.univ
      (fun p _ => MeasureTheory.integrable_finsetSum Finset.univ
        (fun q _ => MeasureTheory.integrable_finsetSum Finset.univ
          (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun s _ => (integrable_repMatrix_entry_star_mul_star ρ μG
              hρcont p q r s).const_mul _))))).trans
      (Finset.sum_congr rfl fun p _ =>
        (MeasureTheory.integral_finsetSum Finset.univ
          (fun q _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
              (fun s _ => (integrable_repMatrix_entry_star_mul_star ρ μG
                hρcont p q r s).const_mul _)))).trans
          (Finset.sum_congr rfl fun q _ =>
            (MeasureTheory.integral_finsetSum Finset.univ
              (fun r _ => MeasureTheory.integrable_finsetSum Finset.univ
                (fun s _ => (integrable_repMatrix_entry_star_mul_star ρ μG
                  hρcont p q r s).const_mul _))).trans
              (Finset.sum_congr rfl fun r _ =>
                MeasureTheory.integral_finsetSum Finset.univ
                  (fun s _ => (integrable_repMatrix_entry_star_mul_star
                    ρ μG hρcont p q r s).const_mul _))))
  have hid1 : (∑ p, ∑ r, star (A i p) * (canonicalForm ρ) p r
        * star (C k r))
      = ((A.map (starRingEnd ℂ)) * canonicalForm ρ * Cᴴ) i k := by
    symm
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
      starRingEnd_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hid2 : (∑ q, ∑ s, star (B q j) * star ((canonicalForm ρ) q s)
        * star (D s l))
      = (Bᴴ * (canonicalForm ρ).map (starRingEnd ℂ)
          * D.map (starRingEnd ℂ)) j l := by
    symm
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
      starRingEnd_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsplit : (∑ p, ∑ q, ∑ r, ∑ s, (star (A i p) * (canonicalForm ρ) p r
          * star (C k r)) * (star (B q j) * star ((canonicalForm ρ) q s)
            * star (D s l)))
      = ((∑ p, ∑ r, star (A i p) * (canonicalForm ρ) p r * star (C k r)))
        * (∑ q, ∑ s, star (B q j) * star ((canonicalForm ρ) q s)
            * star (D s l)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul_sum]
  by_cases hν : fsIndicator ρ μG = 0
  · rw [if_pos hν]
    calc ∫ g, star ((A * repMatrix ρ g * B) i j)
          * star ((C * repMatrix ρ g * D) k l) ∂μG
        = ∑ p, ∑ q, ∑ r, ∑ s, ∫ g, (star (A i p) * star (C k r))
            * (star (B q j) * star (D s l))
            * (star (repMatrix ρ g p q) * star (repMatrix ρ g r s)) ∂μG :=
          (integral_congr_ae (Filter.Eventually.of_forall hexp)).trans hswap
      _ = ∑ p, ∑ q, ∑ r, ∑ s, (0 : ℂ) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
            Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by
              rw [hterm p q r s, if_pos hν, mul_zero]
      _ = 0 := by simp only [Finset.sum_const_zero]
  · rw [if_neg hν]
    calc ∫ g, star ((A * repMatrix ρ g * B) i j)
          * star ((C * repMatrix ρ g * D) k l) ∂μG
        = ∑ p, ∑ q, ∑ r, ∑ s, (star (A i p) * star (C k r))
            * (star (B q j) * star (D s l))
            * ((d : ℂ)⁻¹ * ((canonicalForm ρ) p r
              * star ((canonicalForm ρ) q s))) :=
          (integral_congr_ae (Filter.Eventually.of_forall hexp)).trans
            (hswap.trans (Finset.sum_congr rfl fun p _ =>
              Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl
                fun r _ => Finset.sum_congr rfl fun s _ =>
                  (hterm p q r s).trans (by rw [if_neg hν])))
      _ = (d : ℂ)⁻¹ * ((∑ p, ∑ r, star (A i p) * (canonicalForm ρ) p r
              * star (C k r))
            * (∑ q, ∑ s, star (B q j) * star ((canonicalForm ρ) q s)
              * star (D s l))) := by
          trans (d : ℂ)⁻¹ * (∑ p, ∑ q, ∑ r, ∑ s,
              (star (A i p) * (canonicalForm ρ) p r * star (C k r))
              * (star (B q j) * star ((canonicalForm ρ) q s)
                * star (D s l)))
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
          · rw [hsplit]
      _ = (d : ℂ)⁻¹ * (((A.map (starRingEnd ℂ)) * canonicalForm ρ * Cᴴ) i k
            * (Bᴴ * (canonicalForm ρ).map (starRingEnd ℂ)
              * D.map (starRingEnd ℂ)) j l) := by rw [hid1, hid2]

/-- **R2 closure, Frobenius form.** The contraction that
`charFn_sewing` produces — two path matrices contracted
through `star J` on one index pair and `J` on the other —
regroups as the Frobenius pairing of the `J`-twisted
product `Xᵀ * J * Y` against `J` itself: a finite index
identity, no integration. -/
theorem jContract_frobenius (X Y : Matrix (Fin d) (Fin d) ℂ) :
    (∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d, X p.2 p.1 * Y q.2 q.1
        * (star ((canonicalForm ρ) p.1 q.1) * (canonicalForm ρ) p.2 q.2))
    = ∑ n, ∑ u, (Xᵀ * canonicalForm ρ * Y) n u
        * star ((canonicalForm ρ) n u) := by
  classical
  have hR : (∑ n, ∑ u, (Xᵀ * canonicalForm ρ * Y) n u
        * star ((canonicalForm ρ) n u))
      = ∑ n, ∑ u, ∑ t, ∑ m, ((X m n * (canonicalForm ρ) m t) * Y t u)
          * star ((canonicalForm ρ) n u) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
  rw [hR, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **R2 closure, Gram form.** A self-paired entry sum is
a sum of squared norms: the end form of a closed
contraction whose two sides are conjugate partners. -/
theorem entry_gram_normSq (W : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, ∑ j, W i j * star (W i j))
    = ((∑ i, ∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ i j : Fin d, W i j * star (W i j)
      = ((‖W i j‖ : ℂ)) ^ 2 := by
    intro i j
    rw [mul_comm]
    have h := Complex.conj_mul' (W i j)
    rwa [starRingEnd_eq_star] at h
  calc (∑ i, ∑ j, W i j * star (W i j))
      = ∑ i, ∑ j, ((‖W i j‖ : ℂ)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          hterm i j
    _ = ((∑ i, ∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]

end TwistedContraction

/-! ## §5c-i. Conjugation pairing and the per-pattern evaluation

PW-5c is built in two bricks. This first brick (i) proves
the conjugation pairing: at the diagonal, the character
moment of the complementary pattern `C \ t` is the
conjugate of the moment of `t`, so the sixteen patterns
of a `C4` quad form eight conjugate pairs with equal real
parts; and (ii) evaluates each pattern's moment on the
diagonal as a Frobenius square: the entry expansion of
`quadCharMoment_eq_sum_siteInt` separates into a row
network and a column network, the column network is the
conjugate of the row network, and the moment is
`(d)⁻⁴` times the squared norm of the row network — in
particular its real part is nonnegative, and so is the
real part of each conjugate pair sum.

**Fences.** This section asserts signs only for
per-pattern pair sums of `quadCharMoment` on the
diagonal. It does not assert a sign for `Φ` itself: the
summation over primitive quads and the `e1` baseline are
the second brick's business. NO CLAIM; dials 0/4.
Finite-volume algebra only; `N = 2` is not touched. -/

section PatternEvaluation

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **Conjugation pairing.** At the diagonal, the moment
of the complementary pattern is the conjugate of the
moment of the pattern: the integrand at `C \ t` is
pointwise the conjugate of the integrand at `t`, since
`C \ (C \ t) = t` and conjugation exchanges the plain
and conjugated products. -/
theorem quadCharMoment_compl {C t : Finset (LayerColumn N)} (ht : t ⊆ C)
    (u : LayerLink N → G) :
    quadCharMoment ρ μG C (C \ t) u u
      = star (quadCharMoment ρ μG C t u u) := by
  classical
  have hsd : C \ (C \ t) = t := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxC, hx⟩
      by_contra hxt
      exact hx ⟨hxC, hxt⟩
    · intro hxt
      exact ⟨ht hxt, fun h => h.2 hxt⟩
  have hpt : ∀ α : LayerSite N → G,
      (∏ P ∈ C \ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
        * (∏ P ∈ C \ (C \ t), star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α)))
      = star ((∏ P ∈ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
        * (∏ P ∈ C \ t, star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α)))) := by
    intro α
    rw [hsd]
    simp only [star_mul, star_prod, star_star, mul_comm]
  have hstar : star (∫ α, (∏ P ∈ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
        * (∏ P ∈ C \ t, star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α)))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α, star ((∏ P ∈ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
        * (∏ P ∈ C \ t, star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))))
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
    simpa only [starRingEnd_apply] using
      (integral_conj (μ := (Measure.pi fun _ : LayerSite N => μG))
        (f := fun α => (∏ P ∈ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
          * (∏ P ∈ C \ t, star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))))).symm
  calc quadCharMoment ρ μG C (C \ t) u u
      = ∫ α, (∏ P ∈ C \ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
          * (∏ P ∈ C \ (C \ t), star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α)))
          ∂(Measure.pi fun _ : LayerSite N => μG) := rfl
    _ = ∫ α, star ((∏ P ∈ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
          * (∏ P ∈ C \ t, star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = star (∫ α, (∏ P ∈ t, charFn ρ (colWord u u P.1 P.2.1 P.2.2 α))
          * (∏ P ∈ C \ t, star (charFn ρ (colWord u u P.1 P.2.1 P.2.2 α)))
          ∂(Measure.pi fun _ : LayerSite N => μG)) := hstar.symm
    _ = star (quadCharMoment ρ μG C t u u) := rfl

/-- The real part of a conjugate is the real part. -/
private theorem star_re (z : ℂ) : (star z).re = z.re :=
  Complex.conj_re z

/-- **Pairing, real form.** Complementary patterns have
equal real parts on the diagonal — the form the assembly
consumes. -/
theorem quadCharMoment_compl_re {C t : Finset (LayerColumn N)} (ht : t ⊆ C)
    (u : LayerLink N → G) :
    (quadCharMoment ρ μG C (C \ t) u u).re
      = (quadCharMoment ρ μG C t u u).re := by
  rw [quadCharMoment_compl ρ μG ht u, star_re]

/-- The entry a single column factor contributes at a
site: the `(p, q)` entry of `ρ(g)` when `κ = false`
(the factor is plain), its conjugate when `κ = true`.
Every site factor of §5b is of this form (the table
cells `colSiteFac_base_plain` and its siblings). -/
def entryFac (κ : Bool) (p q : Fin d) (g : G) : ℂ :=
  if κ then star (repMatrix ρ g p q) else repMatrix ρ g p q

private theorem entryFac_false (p q : Fin d) (g : G) :
    entryFac ρ false p q g = repMatrix ρ g p q := rfl

private theorem entryFac_true (p q : Fin d) (g : G) :
    entryFac ρ true p q g = star (repMatrix ρ g p q) := rfl

/-- The **row value** of a pair of entries: what the
pair integral contributes to the row network. Mixed
pairs contribute a Kronecker delta; same-kind pairs
contribute the `J`-tensor entry of PW-3 (row slot),
and vanish when the Frobenius–Schur indicator does. -/
noncomputable def pairRowVal (κ₁ : Bool) (p₁ : Fin d) (κ₂ : Bool)
    (p₂ : Fin d) : ℂ :=
  if κ₁ = κ₂ then
    if fsIndicator ρ μG = 0 then 0
    else if κ₁ then (canonicalForm ρ) p₁ p₂
      else star ((canonicalForm ρ) p₁ p₂)
  else if p₁ = p₂ then 1 else 0

/-- The **column value** of a pair of entries: the
conjugate of the row value read at the column indices.
This is the algebraic content of the column network
being the conjugate of the row network. -/
noncomputable def pairColVal (κ₁ : Bool) (q₁ : Fin d) (κ₂ : Bool)
    (q₂ : Fin d) : ℂ :=
  star (pairRowVal ρ μG κ₁ q₁ κ₂ q₂)

/-- **The pair integral splits.** Integrating a product
of two entry factors over the site variable gives
`(d)⁻¹` times the row value times the column value:
the four owned evaluations (PW-1 mixed, PW-3
same-kind) read in row/column form. -/
theorem integral_entryFac_mul (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (κ₁ κ₂ : Bool) (p₁ q₁ p₂ q₂ : Fin d) :
    ∫ g, entryFac ρ κ₁ p₁ q₁ g * entryFac ρ κ₂ p₂ q₂ g ∂μG
      = (d : ℂ)⁻¹ * pairRowVal ρ μG κ₁ p₁ κ₂ p₂
        * pairColVal ρ μG κ₁ q₁ κ₂ q₂ := by
  classical
  cases κ₁ <;> cases κ₂
  · simp only [entryFac_false]
    rw [integral_repMatrix_mul_repMatrix μG ρ hd hρirr hρcont p₁ q₁ p₂ q₂]
    by_cases hν : fsIndicator ρ μG = 0 <;>
      simp [pairRowVal, pairColVal, hν, mul_assoc]
  · simp only [entryFac_false, entryFac_true]
    rw [integral_repMatrix_mul_star_repMatrix μG ρ hρcont hρirr p₁ q₁ p₂ q₂]
    by_cases hp : p₁ = p₂ <;> by_cases hq : q₁ = q₂ <;>
      simp [pairRowVal, pairColVal, hp, hq]
  · simp only [entryFac_false, entryFac_true]
    rw [integral_star_repMatrix_mul_repMatrix μG ρ hρcont hρirr p₁ q₁ p₂ q₂]
    by_cases hp : p₁ = p₂ <;> by_cases hq : q₁ = q₂ <;>
      simp [pairRowVal, pairColVal, hp, hq]
  · simp only [entryFac_true]
    rw [integral_star_repMatrix_mul_star_repMatrix μG ρ hd hρirr hρcont
      p₁ q₁ p₂ q₂]
    by_cases hν : fsIndicator ρ μG = 0 <;>
      simp [pairRowVal, pairColVal, hν, mul_assoc]

/-- The kind of the factor column `i` contributes at
site `j` of the ordered cycle: at its base the factor
is conjugated exactly when the column is taken
conjugated (`σ i = false`); at its head, exactly when
the column is taken plain. -/
noncomputable def siteKind (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool) (i j : Fin 4) : Bool :=
  if (P i).1 = s j then !(σ i) else σ i

/-- The row index of column `i` at site `j`, read in
the original entry functions: the `a`-index at the
base; at the head, the `f`-index when the column is
plain and the `b`-index when it is conjugated. -/
noncomputable def siteRowIdx (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool)
    (a b e f : Fin 4 → Fin d) (i j : Fin 4) : Fin d :=
  if (P i).1 = s j then a i else if σ i then f i else b i

/-- The column index of column `i` at site `j`: at
the base, the `b`-index when the column is plain and
the `f`-index when it is conjugated; the `e`-index
at the head. -/
noncomputable def siteColIdx (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool)
    (a b e f : Fin 4 → Fin d) (i j : Fin 4) : Fin d :=
  if (P i).1 = s j then (if σ i then b i else f i) else e i

/-- **The site factor is an entry factor.** At an
ordered site, the factor a column contributes is the
entry factor of its kind at its row and column
indices — the table of §5b read through `entryFac`. -/
theorem colSiteFac_eq_entryFac (hN : Even N)
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (σ : Fin 4 → Bool) (a b e f : Fin 4 → Fin d) {i j : Fin 4}
    (hmem : s j ∈ colSites (P i)) (g : G) :
    colSiteFac ρ (P i) (σ i) (a i) (b i) (e i) (f i) (s j) g
      = entryFac ρ (siteKind s P σ i j) (siteRowIdx s P σ a b e f i j)
          (siteColIdx s P σ a b e f i j) g := by
  by_cases hb : (P i).1 = s j
  · rw [colSiteFac_ordered_of_base ρ i j (σ i) a b e f g hb]
    cases hσ : σ i <;>
      simp [siteKind, siteRowIdx, siteColIdx, hb, hσ,
        entryFac_false, entryFac_true]
  · rw [colSiteFac_ordered_of_head ρ hN i j (σ i) a b e f g hmem hb]
    cases hσ : σ i <;>
      simp [siteKind, siteRowIdx, siteColIdx, hb, hσ,
        entryFac_false, entryFac_true]

/-- **The site integral splits.** At an ordered site,
the site integral of R1 is `(d)⁻¹` times the row value
times the column value of the two incident entry
factors. -/
theorem siteInt_eq (hN : Even N) (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)})
    (σ : Fin 4 → Bool) (a b e f : Fin 4 → Fin d) (j : Fin 4) :
    (∫ g, colSiteFac ρ (P (j + 3)) (σ (j + 3)) (a (j + 3)) (b (j + 3))
        (e (j + 3)) (f (j + 3)) (s j) g
      * colSiteFac ρ (P j) (σ j) (a j) (b j) (e j) (f j) (s j) g ∂μG)
    = (d : ℂ)⁻¹
      * pairRowVal ρ μG (siteKind s P σ (j + 3) j)
          (siteRowIdx s P σ a b e f (j + 3) j) (siteKind s P σ j j)
          (siteRowIdx s P σ a b e f j j)
      * pairColVal ρ μG (siteKind s P σ (j + 3) j)
          (siteColIdx s P σ a b e f (j + 3) j) (siteKind s P σ j j)
          (siteColIdx s P σ a b e f j j) := by
  have h43 : ∀ k : Fin 4, k + 3 + 1 = k := by decide
  have hmem1 : s j ∈ colSites (P (j + 3)) := by
    rw [hinc (j + 3), h43 j]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem2 : s j ∈ colSites (P j) := by
    rw [hinc j]
    exact Finset.mem_insert_self _ _
  have hpt : ∀ g : G,
      colSiteFac ρ (P (j + 3)) (σ (j + 3)) (a (j + 3)) (b (j + 3))
          (e (j + 3)) (f (j + 3)) (s j) g
        * colSiteFac ρ (P j) (σ j) (a j) (b j) (e j) (f j) (s j) g
      = entryFac ρ (siteKind s P σ (j + 3) j)
          (siteRowIdx s P σ a b e f (j + 3) j)
          (siteColIdx s P σ a b e f (j + 3) j) g
        * entryFac ρ (siteKind s P σ j j) (siteRowIdx s P σ a b e f j j)
          (siteColIdx s P σ a b e f j j) g := by
    intro g
    rw [colSiteFac_eq_entryFac ρ hN σ a b e f hmem1 g,
      colSiteFac_eq_entryFac ρ hN σ a b e f hmem2 g]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_entryFac_mul ρ μG hd hρirr hρcont _ _ _ _ _ _

/-- The row index of column `i` at site `j` in network
coordinates: the base index `A i` at the base, the
head index `R i` at the head. -/
noncomputable def netRowIdx (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (A R : Fin 4 → Fin d) (i j : Fin 4) : Fin d :=
  if (P i).1 = s j then A i else R i

/-- The column index of column `i` at site `j` in
network coordinates: the base index `Cc i` at the
base, the head index `E i` at the head. -/
noncomputable def netColIdx (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (Cc E : Fin 4 → Fin d) (i j : Fin 4) :
    Fin d :=
  if (P i).1 = s j then Cc i else E i

/-- The **row network** of a pattern on the ordered
cycle: the sum, over base and head row indices, of
the frozen row factors times the row values at the
four sites. -/
noncomputable def rowNetwork (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool)
    (u : LayerLink N → G) : ℂ :=
  ∑ A : Fin 4 → Fin d, ∑ R : Fin 4 → Fin d,
    (∏ i, entryFac ρ (σ i) (A i) (R i) (u (colLink (P i))))
      * ∏ j, pairRowVal ρ μG (siteKind s P σ (j + 3) j)
          (netRowIdx s P A R (j + 3) j) (siteKind s P σ j j)
          (netRowIdx s P A R j j)

/-- The **column network**: the same contraction read
in the column indices, with the conjugated frozen
factors and the column values. -/
noncomputable def colNetwork (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool)
    (u : LayerLink N → G) : ℂ :=
  ∑ Cc : Fin 4 → Fin d, ∑ E : Fin 4 → Fin d,
    (∏ i, entryFac ρ (!(σ i)) (Cc i) (E i) (u (colLink (P i))))
      * ∏ j, pairColVal ρ μG (siteKind s P σ (j + 3) j)
          (netColIdx s P Cc E (j + 3) j) (siteKind s P σ j j)
          (netColIdx s P Cc E j j)

private theorem star_entryFac (κ : Bool) (p q : Fin d) (g : G) :
    star (entryFac ρ κ p q g) = entryFac ρ (!κ) p q g := by
  cases κ <;> simp [entryFac]

/-- **The column network is the conjugate of the row
network.** Conjugation exchanges the two networks
factor by factor: the frozen factors by
`star_entryFac`, the site values by the definition of
`pairColVal`, and the index expressions agree since
`netColIdx` and `netRowIdx` have the same body. -/
theorem colNetwork_eq_star_rowNetwork (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool) (u : LayerLink N → G) :
    colNetwork ρ μG s P σ u = star (rowNetwork ρ μG s P σ u) := by
  have h : ∀ A R : Fin 4 → Fin d,
      (∏ i, entryFac ρ (!(σ i)) (A i) (R i) (u (colLink (P i))))
        * ∏ j, pairColVal ρ μG (siteKind s P σ (j + 3) j)
            (netColIdx s P A R (j + 3) j) (siteKind s P σ j j)
            (netColIdx s P A R j j)
      = star ((∏ i, entryFac ρ (σ i) (A i) (R i) (u (colLink (P i))))
        * ∏ j, pairRowVal ρ μG (siteKind s P σ (j + 3) j)
            (netRowIdx s P A R (j + 3) j) (siteKind s P σ j j)
            (netRowIdx s P A R j j)) := by
    intro A R
    have hCV : (∏ j, pairColVal ρ μG (siteKind s P σ (j + 3) j)
          (netColIdx s P A R (j + 3) j) (siteKind s P σ j j)
          (netColIdx s P A R j j))
        = ∏ j, star (pairRowVal ρ μG (siteKind s P σ (j + 3) j)
            (netRowIdx s P A R (j + 3) j) (siteKind s P σ j j)
            (netRowIdx s P A R j j)) :=
      Finset.prod_congr rfl fun j _ => rfl
    have hF : (∏ i, entryFac ρ (!(σ i)) (A i) (R i) (u (colLink (P i))))
        = ∏ i, star (entryFac ρ (σ i) (A i) (R i)
            (u (colLink (P i)))) :=
      Finset.prod_congr rfl fun i _ => (star_entryFac ρ _ _ _ _).symm
    rw [star_mul, star_prod, star_prod,
      mul_comm (∏ i, entryFac ρ (!(σ i)) (A i) (R i) (u (colLink (P i))))
        (∏ j, pairColVal ρ μG (siteKind s P σ (j + 3) j)
          (netColIdx s P A R (j + 3) j) (siteKind s P σ j j)
          (netColIdx s P A R j j)), hCV, hF]
  simp only [rowNetwork, star_sum]
  rw [colNetwork]
  exact Finset.sum_congr rfl fun A _ =>
    Finset.sum_congr rfl fun R _ => h A R

/-- The frozen factor on the diagonal splits as the
row frozen factor times the column frozen factor:
with row indices `(a, if σ then f else b)` and column
indices `(if σ then b else f, e)`. -/
theorem colFrozenFac_diag (u : LayerLink N → G) (Q : LayerColumn N)
    (σ : Bool) (a b e f : Fin d) :
    colFrozenFac ρ u u Q σ a b e f
      = entryFac ρ σ a (if σ then f else b) (u (colLink Q))
        * entryFac ρ (!σ) (if σ then b else f) e (u (colLink Q)) := by
  cases σ <;> simp [colFrozenFac, entryFac, mul_comm]

/-- **The summand splits.** One summand of R1's entry
expansion, on the diagonal, is `((d)⁻¹)⁴` times the
row part (frozen row factors times site row values)
times the column part: the frozen factors split by
`colFrozenFac_diag`, the site integrals by
`siteInt_eq`, and the products regroup. -/
theorem summand_split (hN : Even N) (hd : 0 < d)
    (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {s : Fin 4 → LayerSite N} {P : Fin 4 → LayerColumn N}
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)})
    (σ : Fin 4 → Bool) (u : LayerLink N → G) (a b e f : Fin 4 → Fin d) :
    (∏ i, colFrozenFac ρ u u (P i) (σ i) (a i) (b i) (e i) (f i))
      * ∏ j, (∫ g, colSiteFac ρ (P (j + 3)) (σ (j + 3)) (a (j + 3))
          (b (j + 3)) (e (j + 3)) (f (j + 3)) (s j) g
        * colSiteFac ρ (P j) (σ j) (a j) (b j) (e j) (f j) (s j) g ∂μG)
    = ((d : ℂ)⁻¹) ^ 4
      * ((∏ i, entryFac ρ (σ i) (a i) (if σ i then f i else b i)
            (u (colLink (P i))))
        * ∏ j, pairRowVal ρ μG (siteKind s P σ (j + 3) j)
            (siteRowIdx s P σ a b e f (j + 3) j) (siteKind s P σ j j)
            (siteRowIdx s P σ a b e f j j))
      * ((∏ i, entryFac ρ (!(σ i)) (if σ i then b i else f i) (e i)
            (u (colLink (P i))))
        * ∏ j, pairColVal ρ μG (siteKind s P σ (j + 3) j)
            (siteColIdx s P σ a b e f (j + 3) j) (siteKind s P σ j j)
            (siteColIdx s P σ a b e f j j)) := by
  have hF : (∏ i, colFrozenFac ρ u u (P i) (σ i) (a i) (b i) (e i) (f i))
      = ∏ i, (entryFac ρ (σ i) (a i) (if σ i then f i else b i)
            (u (colLink (P i)))
        * entryFac ρ (!(σ i)) (if σ i then b i else f i) (e i)
            (u (colLink (P i)))) :=
    Finset.prod_congr rfl fun i _ =>
      colFrozenFac_diag ρ u (P i) (σ i) (a i) (b i) (e i) (f i)
  have hS : (∏ j, (∫ g, colSiteFac ρ (P (j + 3)) (σ (j + 3)) (a (j + 3))
          (b (j + 3)) (e (j + 3)) (f (j + 3)) (s j) g
        * colSiteFac ρ (P j) (σ j) (a j) (b j) (e j) (f j) (s j) g ∂μG))
      = ∏ j, ((d : ℂ)⁻¹
        * pairRowVal ρ μG (siteKind s P σ (j + 3) j)
            (siteRowIdx s P σ a b e f (j + 3) j) (siteKind s P σ j j)
            (siteRowIdx s P σ a b e f j j)
        * pairColVal ρ μG (siteKind s P σ (j + 3) j)
            (siteColIdx s P σ a b e f (j + 3) j) (siteKind s P σ j j)
            (siteColIdx s P σ a b e f j j)) :=
    Finset.prod_congr rfl fun j _ =>
      siteInt_eq ρ μG hN hd hρirr hρcont hinc σ a b e f j
  rw [hF, hS]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-- The coordinate swap on a pair of entry functions:
per column, the row partner reads `f` where the pattern
bit is set and `b` where it is not; the column partner
reads the complementary choice. -/
def swapFun (σ : Fin 4 → Bool)
    (bf : (Fin 4 → Fin d) × (Fin 4 → Fin d)) :
    (Fin 4 → Fin d) × (Fin 4 → Fin d) :=
  (fun i => if σ i then bf.2 i else bf.1 i,
    fun i => if σ i then bf.1 i else bf.2 i)

private theorem swapFun_involutive (σ : Fin 4 → Bool) :
    Function.Involutive
      (swapFun σ : (Fin 4 → Fin d) × (Fin 4 → Fin d)
        → (Fin 4 → Fin d) × (Fin 4 → Fin d)) := by
  intro bf
  refine Prod.ext ?_ ?_ <;> funext i <;> simp only [swapFun]
    <;> cases h : σ i <;> simp [h]

/-- The swap as an equivalence on pairs of entry
functions. -/
def swapPair (σ : Fin 4 → Bool) :
    (Fin 4 → Fin d) × (Fin 4 → Fin d)
      ≃ (Fin 4 → Fin d) × (Fin 4 → Fin d) :=
  (swapFun_involutive σ).toPerm (swapFun σ)

/-- Reindexing a double sum by the swap: summing `H`
over `(b, f)` is summing `H` over the swapped
coordinates `(row partner, column partner)`. -/
theorem sum_reindex_swap (σ : Fin 4 → Bool)
    (H : (Fin 4 → Fin d) → (Fin 4 → Fin d) → ℂ) :
    (∑ b, ∑ f, H b f)
      = ∑ R, ∑ Cc, H (swapFun σ (R, Cc)).1 (swapFun σ (R, Cc)).2 := by
  calc (∑ b, ∑ f, H b f) = ∑ x : (Fin 4 → Fin d) × (Fin 4 → Fin d),
        H x.1 x.2 := (Fintype.sum_prod_type (fun x => H x.1 x.2)).symm
    _ = ∑ x : (Fin 4 → Fin d) × (Fin 4 → Fin d),
        H ((swapPair σ) x).1 ((swapPair σ) x).2 :=
      (Equiv.sum_comp (swapPair σ) (fun x => H x.1 x.2)).symm
    _ = ∑ R, ∑ Cc, H (swapFun σ (R, Cc)).1 (swapFun σ (R, Cc)).2 := by
      simp only [swapPair, Function.Involutive.coe_toPerm]
      exact Fintype.sum_prod_type _

/-- Swapping two nested entry-function sums, via the
product form and the coordinate commutation
equivalence. -/
theorem sum_comm_swap
    (F : (Fin 4 → Fin d) → (Fin 4 → Fin d) → ℂ) :
    (∑ a, ∑ b, F a b) = ∑ b, ∑ a, F a b := by
  calc (∑ a, ∑ b, F a b)
      = ∑ x : (Fin 4 → Fin d) × (Fin 4 → Fin d), F x.1 x.2 :=
        (Fintype.sum_prod_type (fun x => F x.1 x.2)).symm
    _ = ∑ x : (Fin 4 → Fin d) × (Fin 4 → Fin d), F x.2 x.1 :=
        Equiv.sum_comp (Equiv.prodComm _ _) (fun x => F x.2 x.1)
    _ = ∑ b, ∑ a, F a b :=
        Fintype.sum_prod_type (fun x => F x.2 x.1)

/-- **Frobenius factorization (L5).** On the diagonal,
a pattern moment over a C4 column splits as
`((d)⁻¹)⁴` times the row network times the column
network: R1's entry expansion, each summand split by
`summand_split`, and the `(b, f)` sums reindexed by
the coordinate swap. -/
theorem quadCharMoment_eq_rowNetwork_mul (hN : Even N) (hd : 0 < d)
    (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {C : Finset (LayerColumn N)} {s : Fin 4 → LayerSite N}
    {P : Fin 4 → LayerColumn N}
    (hs : Function.Injective s) (hP : Function.Injective P)
    (hPmem : ∀ i, P i ∈ C) (hPcover : ∀ Q ∈ C, ∃ i, P i = Q)
    (hinc : ∀ i, colSites (P i) = {s i, s (i + 1)})
    {t : Finset (LayerColumn N)} (ht : t ⊆ C) (u : LayerLink N → G) :
    quadCharMoment ρ μG C t u u
      = ((d : ℂ)⁻¹) ^ 4
        * (rowNetwork ρ μG s P (fun i => decide (P i ∈ t)) u
          * colNetwork ρ μG s P (fun i => decide (P i ∈ t)) u) := by
  classical
  calc quadCharMoment ρ μG C t u u
      = ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d,
        ∑ e : Fin 4 → Fin d, ∑ f : Fin 4 → Fin d,
          (∏ i, colFrozenFac ρ u u (P i) (decide (P i ∈ t)) (a i)
              (b i) (e i) (f i))
          * ∏ j, (∫ g, colSiteFac ρ (P (j + 3))
              (decide (P (j + 3) ∈ t)) (a (j + 3)) (b (j + 3))
              (e (j + 3)) (f (j + 3)) (s j) g
            * colSiteFac ρ (P j) (decide (P j ∈ t)) (a j) (b j)
              (e j) (f j) (s j) g ∂μG) :=
      quadCharMoment_eq_sum_siteInt ρ μG hN hρcont hs hP hPmem
        hPcover hinc ht u u
    _ = ∑ a : Fin 4 → Fin d, ∑ b : Fin 4 → Fin d,
        ∑ e : Fin 4 → Fin d, ∑ f : Fin 4 → Fin d,
          ((d : ℂ)⁻¹) ^ 4
          * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i)
                (if decide (P i ∈ t) then f i else b i)
                (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (siteRowIdx s P (fun i => decide (P i ∈ t)) a b e f
                  (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (siteRowIdx s P (fun i => decide (P i ∈ t)) a b e f
                  j j))
          * ((∏ i, entryFac ρ (!(decide (P i ∈ t)))
                (if decide (P i ∈ t) then b i else f i) (e i)
                (u (colLink (P i))))
            * ∏ j, pairColVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (siteColIdx s P (fun i => decide (P i ∈ t)) a b e f
                  (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (siteColIdx s P (fun i => decide (P i ∈ t)) a b e f
                  j j)) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ =>
          summand_split ρ μG hN hd hρirr hρcont hinc
            (fun i => decide (P i ∈ t)) u a b e f
    _ = ∑ a : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
        ∑ b : Fin 4 → Fin d, ∑ f : Fin 4 → Fin d,
          ((d : ℂ)⁻¹) ^ 4
          * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i)
                (if decide (P i ∈ t) then f i else b i)
                (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (siteRowIdx s P (fun i => decide (P i ∈ t)) a b e f
                  (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (siteRowIdx s P (fun i => decide (P i ∈ t)) a b e f
                  j j))
          * ((∏ i, entryFac ρ (!(decide (P i ∈ t)))
                (if decide (P i ∈ t) then b i else f i) (e i)
                (u (colLink (P i))))
            * ∏ j, pairColVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (siteColIdx s P (fun i => decide (P i ∈ t)) a b e f
                  (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (siteColIdx s P (fun i => decide (P i ∈ t)) a b e f
                  j j)) :=
      Finset.sum_congr rfl fun a _ => sum_comm_swap _
    _ = ∑ a : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
        ∑ R : Fin 4 → Fin d, ∑ Cc : Fin 4 → Fin d,
          ((d : ℂ)⁻¹) ^ 4
          * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i)
                (if decide (P i ∈ t)
                  then (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2 i
                  else (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 i)
                (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (siteRowIdx s P (fun i => decide (P i ∈ t)) a
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                  (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (siteRowIdx s P (fun i => decide (P i ∈ t)) a
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                  j j))
          * ((∏ i, entryFac ρ (!(decide (P i ∈ t)))
                (if decide (P i ∈ t)
                  then (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 i
                  else (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2 i)
                (e i) (u (colLink (P i))))
            * ∏ j, pairColVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (siteColIdx s P (fun i => decide (P i ∈ t)) a
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                  (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (siteColIdx s P (fun i => decide (P i ∈ t)) a
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                  j j)) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ =>
        sum_reindex_swap (fun i => decide (P i ∈ t)) _
    _ = ∑ a : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
        ∑ R : Fin 4 → Fin d, ∑ Cc : Fin 4 → Fin d,
          ((d : ℂ)⁻¹) ^ 4
          * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netRowIdx s P a R (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netRowIdx s P a R j j))
          * ((∏ i, entryFac ρ (!(decide (P i ∈ t))) (Cc i) (e i)
                (u (colLink (P i))))
            * ∏ j, pairColVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netColIdx s P Cc e (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netColIdx s P Cc e j j)) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ =>
        Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl
          fun Cc _ => by
            have hcol1 : ∀ i, (if decide (P i ∈ t)
                  then (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2 i
                  else (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 i)
                = R i := by
              intro i
              exact congrFun (congrArg Prod.fst
                (swapFun_involutive (fun i => decide (P i ∈ t)) (R, Cc))) i
            have hcol2 : ∀ i, (if decide (P i ∈ t)
                  then (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 i
                  else (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2 i)
                = Cc i := by
              intro i
              exact congrFun (congrArg Prod.snd
                (swapFun_involutive (fun i => decide (P i ∈ t)) (R, Cc))) i
            have hsiteR : ∀ i j, siteRowIdx s P
                  (fun i => decide (P i ∈ t)) a
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2 i j
                = netRowIdx s P a R i j := by
              intro i j
              by_cases hb : (P i).1 = s j
              · simp only [siteRowIdx, netRowIdx, hb, if_true]
              · simp only [siteRowIdx, netRowIdx, hb, if_false]
                exact hcol1 i
            have hsiteC : ∀ i j, siteColIdx s P
                  (fun i => decide (P i ∈ t)) a
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                  (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2 i j
                = netColIdx s P Cc e i j := by
              intro i j
              by_cases hb : (P i).1 = s j
              · simp only [siteColIdx, netColIdx, hb, if_true]
                exact hcol2 i
              · simp only [siteColIdx, netColIdx, hb, if_false]
            rw [Finset.prod_congr rfl (s₁ := Finset.univ)
              (fun i _ => by rw [hcol1 i] :
                ∀ i ∈ (Finset.univ : Finset (Fin 4)),
                  entryFac ρ (decide (P i ∈ t)) (a i)
                    (if decide (P i ∈ t)
                      then (swapFun (fun i => decide (P i ∈ t))
                        (R, Cc)).2 i
                      else (swapFun (fun i => decide (P i ∈ t))
                        (R, Cc)).1 i) (u (colLink (P i)))
                    = entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                      (u (colLink (P i))))]
            rw [Finset.prod_congr rfl (s₁ := Finset.univ)
              (fun j _ => by rw [hsiteR (j + 3) j, hsiteR j j] :
                ∀ j ∈ (Finset.univ : Finset (Fin 4)),
                  pairRowVal ρ μG
                    (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                    (siteRowIdx s P (fun i => decide (P i ∈ t)) a
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                      (j + 3) j)
                    (siteKind s P (fun i => decide (P i ∈ t)) j j)
                    (siteRowIdx s P (fun i => decide (P i ∈ t)) a
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                      j j)
                  = pairRowVal ρ μG
                    (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                    (netRowIdx s P a R (j + 3) j)
                    (siteKind s P (fun i => decide (P i ∈ t)) j j)
                    (netRowIdx s P a R j j))]
            rw [Finset.prod_congr rfl (s₁ := Finset.univ)
              (fun i _ => by rw [hcol2 i] :
                ∀ i ∈ (Finset.univ : Finset (Fin 4)),
                  entryFac ρ (!(decide (P i ∈ t)))
                    (if decide (P i ∈ t)
                      then (swapFun (fun i => decide (P i ∈ t))
                        (R, Cc)).1 i
                      else (swapFun (fun i => decide (P i ∈ t))
                        (R, Cc)).2 i) (e i) (u (colLink (P i)))
                    = entryFac ρ (!(decide (P i ∈ t))) (Cc i) (e i)
                      (u (colLink (P i))))]
            rw [Finset.prod_congr rfl (s₁ := Finset.univ)
              (fun j _ => by rw [hsiteC (j + 3) j, hsiteC j j] :
                ∀ j ∈ (Finset.univ : Finset (Fin 4)),
                  pairColVal ρ μG
                    (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                    (siteColIdx s P (fun i => decide (P i ∈ t)) a
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                      (j + 3) j)
                    (siteKind s P (fun i => decide (P i ∈ t)) j j)
                    (siteColIdx s P (fun i => decide (P i ∈ t)) a
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).1 e
                      (swapFun (fun i => decide (P i ∈ t)) (R, Cc)).2
                      j j)
                  = pairColVal ρ μG
                    (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                    (netColIdx s P Cc e (j + 3) j)
                    (siteKind s P (fun i => decide (P i ∈ t)) j j)
                    (netColIdx s P Cc e j j))]
    _ = ∑ a : Fin 4 → Fin d, ∑ R : Fin 4 → Fin d,
        ∑ e : Fin 4 → Fin d, ∑ Cc : Fin 4 → Fin d,
          ((d : ℂ)⁻¹) ^ 4
          * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netRowIdx s P a R (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netRowIdx s P a R j j))
          * ((∏ i, entryFac ρ (!(decide (P i ∈ t))) (Cc i) (e i)
                (u (colLink (P i))))
            * ∏ j, pairColVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netColIdx s P Cc e (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netColIdx s P Cc e j j)) :=
      Finset.sum_congr rfl fun a _ => sum_comm_swap _
    _ = ((d : ℂ)⁻¹) ^ 4
        * (rowNetwork ρ μG s P (fun i => decide (P i ∈ t)) u
          * colNetwork ρ μG s P (fun i => decide (P i ∈ t)) u) := by
      have hIn : ∀ (a R : Fin 4 → Fin d),
          (∑ e : Fin 4 → Fin d, ∑ Cc : Fin 4 → Fin d,
            ((d : ℂ)⁻¹) ^ 4
            * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                  (u (colLink (P i))))
              * ∏ j, pairRowVal ρ μG
                  (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                  (netRowIdx s P a R (j + 3) j)
                  (siteKind s P (fun i => decide (P i ∈ t)) j j)
                  (netRowIdx s P a R j j))
            * ((∏ i, entryFac ρ (!(decide (P i ∈ t))) (Cc i) (e i)
                  (u (colLink (P i))))
              * ∏ j, pairColVal ρ μG
                  (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                  (netColIdx s P Cc e (j + 3) j)
                  (siteKind s P (fun i => decide (P i ∈ t)) j j)
                  (netColIdx s P Cc e j j)))
          = (((d : ℂ)⁻¹) ^ 4
            * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                  (u (colLink (P i))))
              * ∏ j, pairRowVal ρ μG
                  (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                  (netRowIdx s P a R (j + 3) j)
                  (siteKind s P (fun i => decide (P i ∈ t)) j j)
                  (netRowIdx s P a R j j)))
            * colNetwork ρ μG s P (fun i => decide (P i ∈ t)) u := by
        intro a R
        simp only [← Finset.mul_sum]
        rw [sum_comm_swap (fun (e Cc : Fin 4 → Fin d) =>
          (∏ i, entryFac ρ (!(decide (P i ∈ t))) (Cc i) (e i)
              (u (colLink (P i))))
            * ∏ j, pairColVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netColIdx s P Cc e (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netColIdx s P Cc e j j))]
        rfl
      have hK : (∑ a : Fin 4 → Fin d, ∑ R : Fin 4 → Fin d,
            ((d : ℂ)⁻¹ ^ 4
              * ∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                  (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netRowIdx s P a R (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netRowIdx s P a R j j))
          = (d : ℂ)⁻¹ ^ 4 * ∑ a : Fin 4 → Fin d, ∑ R : Fin 4 → Fin d,
            (∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                (u (colLink (P i))))
            * ∏ j, pairRowVal ρ μG
                (siteKind s P (fun i => decide (P i ∈ t)) (j + 3) j)
                (netRowIdx s P a R (j + 3) j)
                (siteKind s P (fun i => decide (P i ∈ t)) j j)
                (netRowIdx s P a R j j) := by
        simp only [mul_assoc, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl (s₁ := Finset.univ)
        (fun a _ => Finset.sum_congr rfl (s₁ := Finset.univ)
          (fun R _ => hIn a R) :
          ∀ a ∈ (Finset.univ : Finset (Fin 4 → Fin d)),
            (∑ R : Fin 4 → Fin d, ∑ e : Fin 4 → Fin d,
              ∑ Cc : Fin 4 → Fin d,
                ((d : ℂ)⁻¹) ^ 4
                * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                      (u (colLink (P i))))
                  * ∏ j, pairRowVal ρ μG
                      (siteKind s P (fun i => decide (P i ∈ t))
                        (j + 3) j)
                      (netRowIdx s P a R (j + 3) j)
                      (siteKind s P (fun i => decide (P i ∈ t)) j j)
                      (netRowIdx s P a R j j))
                * ((∏ i, entryFac ρ (!(decide (P i ∈ t))) (Cc i) (e i)
                      (u (colLink (P i))))
                  * ∏ j, pairColVal ρ μG
                      (siteKind s P (fun i => decide (P i ∈ t))
                        (j + 3) j)
                      (netColIdx s P Cc e (j + 3) j)
                      (siteKind s P (fun i => decide (P i ∈ t)) j j)
                      (netColIdx s P Cc e j j)))
            = ∑ R : Fin 4 → Fin d,
                (((d : ℂ)⁻¹) ^ 4
                * ((∏ i, entryFac ρ (decide (P i ∈ t)) (a i) (R i)
                      (u (colLink (P i))))
                  * ∏ j, pairRowVal ρ μG
                      (siteKind s P (fun i => decide (P i ∈ t))
                        (j + 3) j)
                      (netRowIdx s P a R (j + 3) j)
                      (siteKind s P (fun i => decide (P i ∈ t)) j j)
                      (netRowIdx s P a R j j)))
                * colNetwork ρ μG s P (fun i => decide (P i ∈ t)) u)]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, rowNetwork,
        colNetwork, ← mul_assoc]
      rw [hK]

/-- **One moment has nonnegative real part.** At a
C4 (irreducible `ρ`, `0 < d`), the factorized moment
is `((d)⁻¹)⁴` times `RN * star RN`, a nonnegative
real multiple of a squared norm. -/
theorem quadCharMoment_moment_re_nonneg (hN : Even N) (hN3 : 3 ≤ N)
    (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {C : Finset (LayerColumn N)} (hCmem : C ∈ primitiveQuads)
    {t : Finset (LayerColumn N)} (ht : t ⊆ C) (u : LayerLink N → G) :
    0 ≤ (quadCharMoment ρ μG C t u u).re := by
  obtain ⟨s, P, hs, hP, hPmem, hPcover, hinc⟩ :=
    c4_cycle_ordering hN hN3 hCmem
  rw [quadCharMoment_eq_rowNetwork_mul ρ μG hN hd hρirr hρcont hs hP
    hPmem hPcover hinc ht u,
    colNetwork_eq_star_rowNetwork ρ μG s P (fun i => decide (P i ∈ t)) u]
  set RN := rowNetwork ρ μG s P (fun i => decide (P i ∈ t)) u with hRN
  have h1 : RN * star RN = ((‖RN‖ ^ 2 : ℝ) : ℂ) := by
    have h := RCLike.mul_conj RN
    rw [starRingEnd_apply, ← RCLike.ofReal_pow] at h
    exact h
  have hdcast : ((d : ℂ)⁻¹) ^ 4 = (((d : ℝ)⁻¹ ^ 4 : ℝ) : ℂ) := by
    have h : ((d : ℂ)⁻¹) ^ 4 = RCLike.ofReal (((d : ℝ)⁻¹) ^ 4) := by
      rw [RCLike.ofReal_pow, ← RCLike.algebraMap_eq_ofReal, map_inv₀,
        map_natCast]
    exact h
  rw [h1, hdcast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d)) 4)
    (pow_nonneg (norm_nonneg _) 2)

/-- **Per-pattern pair nonnegativity (L7 headline).**
For every pattern `t` of a C4 column `C` (irreducible
`ρ`, `0 < d`), the conjugate pair's sum has
nonnegative real part: the complement moment is the
star of the moment (L1), and one moment already has
nonnegative real part. This closes every pattern
class of the scoping at once — the row/column
network separation is the Gram form. -/
theorem quadCharMoment_pair_nonneg (hN : Even N) (hN3 : 3 ≤ N)
    (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {C : Finset (LayerColumn N)} (hCmem : C ∈ primitiveQuads)
    {t : Finset (LayerColumn N)} (ht : t ⊆ C) (u : LayerLink N → G) :
    0 ≤ (quadCharMoment ρ μG C t u u
      + quadCharMoment ρ μG C (C \ t) u u).re := by
  have h1 := quadCharMoment_moment_re_nonneg ρ μG hN hN3 hd hρirr hρcont
    hCmem ht u
  have h2 := quadCharMoment_compl_re ρ μG ht u
  rw [Complex.add_re, h2]
  exact add_nonneg h1 h1

end PatternEvaluation

/-! ## §5c-ii. The endpoint assembly

The endpoint of the PW line: the diagonal sign of
`κ₄^dep` at order `β⁴`. Scope, on the face:
irreducible `ρ`, even `N ≥ 4`, the diagonal `u' = u`
only. Untouched: orders `β⁵` and beyond; the
off-diagonal functional `Φ(u, u')`; reducible `ρ`;
`𝒜 ⪰ 0` in the large; `N = 2`. No cushion: nothing
here bounds `Φ` away from `0` — the Gram squares of
§PatternEvaluation can degenerate at special
configurations, exactly as the probed seats showed.
NO CLAIM; dials 0/4. -/

section EndpointAssembly

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **Case (a) core.** At `0 < d` with `ρ`
irreducible, every primitive quad's diagonal moment
is nonnegative: by `quadReMoment_primitive_eq` it is
`2⁻⁴` times the sum of the real parts of the pattern
moments, each nonnegative by
`quadCharMoment_moment_re_nonneg`. -/
theorem quadReMoment_nonneg_of_pos (hN : Even N) (hN3 : 3 ≤ N)
    (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {C : Finset (LayerColumn N)} (hC : C ∈ primitiveQuads)
    (u : LayerLink N → G) : 0 ≤ quadReMoment ρ μG C u u := by
  rw [quadReMoment_primitive_eq ρ μG hρcont (isPrimitiveQuad_of_mem hC) u u]
  apply mul_nonneg (pow_nonneg (inv_nonneg.mpr (by norm_num)) 4)
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun t ht => ?_
  exact quadCharMoment_moment_re_nonneg ρ μG hN hN3 hd hρirr hρcont hC
    (Finset.mem_powerset.mp ht) u

/-- **Case (b) bridge.** At `d = 1`, a character
identically `1` forces the representation itself to
be trivial: a `1 × 1` matrix is its single entry,
and by `charFn_eq_entry_of_dim_one` the entry is
the character. This converts the case split's
`¬ ∃ h, charFn ρ h ≠ 1` into the `∀ g, repMatrix ρ g
= 1` hypothesis the E1Pack trivial-case lemmas
consume. -/
theorem repMatrix_eq_one_of_dim_one_of_charFn_eq_one
    (hd : d = 1) (hχ : ∀ g, charFn ρ g = 1) :
    ∀ g, repMatrix ρ g = 1 := by
  subst hd
  intro g
  have h00 : repMatrix ρ g ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    have h := charFn_eq_entry_of_dim_one ρ rfl g
    rw [hχ g] at h
    exact h.symm
  ext i j
  have hi : i = ⟨0, by omega⟩ := by
    rw [Fin.eq_zero i]; exact Fin.mk_zero.symm
  have hj : j = ⟨0, by omega⟩ := by
    rw [Fin.eq_zero j]; exact Fin.mk_zero.symm
  rw [hi, hj,
    show (1 : Matrix (Fin 1) (Fin 1) ℂ) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1
      from Matrix.one_apply_eq _]
  exact h00

/-- **Case (c), character.** At `d = 0` the character
vanishes identically: it is a trace over `Fin 0`. -/
theorem charFn_eq_zero_of_dim_zero (hd : d = 0) (g : G) :
    charFn ρ g = 0 := by
  subst hd
  simp [charFn, Matrix.trace]

/-- **Case (c), moment.** At `d = 0` every column
factor `colRe` vanishes, so the diagonal
`quadReMoment` of a (nonempty) primitive quad is
`0`: its integrand is a product with a zero factor. -/
theorem quadReMoment_eq_zero_of_dim_zero (hd : d = 0)
    {C : Finset (LayerColumn N)} (hC : IsPrimitiveQuad C)
    (u : LayerLink N → G) : quadReMoment ρ μG C u u = 0 := by
  obtain ⟨P, hP⟩ : ∃ P, P ∈ C := by
    have hcard : 0 < C.card := by rw [hC.1]; norm_num
    exact Finset.card_pos.mp hcard
  have hcol : ∀ (Q : LayerColumn N) (α : LayerSite N → G),
      colRe ρ u u Q α = 0 := by
    intro Q α
    show (charFn ρ _).re = 0
    rw [charFn_eq_zero_of_dim_zero ρ hd]
    simp
  have hprod : ∀ α : LayerSite N → G,
      ∏ Q ∈ C, colRe ρ u u Q α = 0 :=
    fun α => Finset.prod_eq_zero hP (hcol P α)
  show (∫ α, ∏ Q ∈ C, colRe ρ u u Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)) = 0
  rw [show (fun α : LayerSite N → G => ∏ Q ∈ C, colRe ρ u u Q α)
      = fun _ => (0 : ℝ) from funext hprod]
  simp

/-- **Case (c), baseline.** At `d = 0`, `e1 = 0`. -/
theorem e1_eq_zero_of_dim_zero (hd : d = 0) : e1 ρ μG = 0 := by
  show (∫ g, (charFn ρ g).re ∂μG) = 0
  rw [show (fun g => (charFn ρ g).re) = fun _ => (0 : ℝ) from
    funext fun g => by rw [charFn_eq_zero_of_dim_zero ρ hd]; simp]
  simp

/-- **Per-quad summand of `Φ`, nonnegative.** The
case split is exhaustive at irreducible `ρ`:
`d = 0` (case (c): moment and baseline both `0`);
`d = 1` nontrivial (baseline `0`, case (a) core);
`d = 1` trivial (moment `1`, baseline `1`, summand
`0`); `2 ≤ d` (baseline `0`, case (a) core). -/
theorem quadReMoment_sub_e1_nonneg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) {C : Finset (LayerColumn N)}
    (hC : C ∈ primitiveQuads) (u : LayerLink N → G) :
    0 ≤ quadReMoment ρ μG C u u - (e1 ρ μG) ^ 4 := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [quadReMoment_eq_zero_of_dim_zero ρ μG hd0
      (isPrimitiveQuad_of_mem hC) u, e1_eq_zero_of_dim_zero ρ μG hd0]
    norm_num
  · rcases (show d = 1 ∨ 2 ≤ d by omega) with hd1 | hd2
    · by_cases hne : ∃ h : G, charFn ρ h ≠ 1
      · rw [e1_eq_zero_of_dim_one_ne ρ μG hd1 hρcont hne,
          zero_pow (by norm_num : (4 : ℕ) ≠ 0), sub_zero]
        exact quadReMoment_nonneg_of_pos ρ μG hN hN3 hdpos hρirr
          hρcont hC u
      · push_neg at hne
        have htriv : ∀ g, repMatrix ρ g = 1 :=
          repMatrix_eq_one_of_dim_one_of_charFn_eq_one ρ hd1 hne
        rw [quadReMoment_eq_one_of_dim_one_trivial ρ μG hd1 htriv C u,
          e1_eq_one_of_dim_one_trivial ρ μG hd1 htriv]
        norm_num
    · rw [e1_eq_zero_of_irreducible ρ μG hρirr hd2 hρcont,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), sub_zero]
      exact quadReMoment_nonneg_of_pos ρ μG hN hN3 hdpos hρirr
        hρcont hC u

/-- **The endpoint: `Φ` is nonnegative on the
diagonal.** At irreducible `ρ`, even `N ≥ 4`, the
sum over the primitive quads of the per-quad
summands is nonnegative, summand by summand. -/
theorem phi_diag_nonneg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (u : LayerLink N → G) :
    0 ≤ phiFunctional ρ μG u := by
  show 0 ≤ ∑ C ∈ primitiveQuads,
    (quadReMoment ρ μG C u u - (e1 ρ μG) ^ 4)
  refine Finset.sum_nonneg fun C hC => ?_
  exact quadReMoment_sub_e1_nonneg ρ μG hN hN3 hρcont hρirr hC u

/-- **The endpoint, transferred: `κ₄^dep` is
nonnegative on the diagonal.** The diagonal sign of
the `β⁴` dependent coefficient, at irreducible `ρ`,
even `N ≥ 4` — via `κ₄^dep (u, u) = d⁻⁴ · Φ(u)` and
`phi_diag_nonneg`. -/
theorem kappa4dep_diag_nonneg (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hρirr : RepIrreducible ρ) (u : LayerLink N → G) :
    0 ≤ kappa4dep ρ μG u u :=
  kappa4dep_diag_nonneg_of_phi_nonneg ρ μG u hN hN3 hρcont
    (phi_diag_nonneg ρ μG hN hN3 hρcont hρirr u)

end EndpointAssembly

end ThetLogos
