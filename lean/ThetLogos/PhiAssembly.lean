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

end ThetLogos
