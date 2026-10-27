import ThetLogos.PolymerActivity
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# LOC-2 — the polymer species and the Kirkwood–Salsburg criterion

The polymer gas over the layer columns of `PolymerActivity`:
connected column-supports of size `≥ 3` (LOC-1: every two-column
connected activity vanishes identically, so genuinely connected
species start at three columns), each column carrying a
non-vacuum degree label, with the product-form activity built
from LOC-1's single-column activities. The landed majorant
`(2|β|)ᵏ/k!` is the only one used (the LOC-0 memo's
`(2β/d)ᵏ/k!` form is false; see the LOC-1 record).

Contents: the column adjacency graph from the owned lattice
geometry (spatial sites `(ZMod N)³`, three directions per site),
with degree `≤ 26` uniformly in `N`; the polymer species as a
type; the per-support degree sum; the animal bound; and the
Kirkwood–Salsburg / Kotecký–Preiss criterion with the explicit
radius `β₀ = (1/2)·ln(1 + 1/(2·729·e))`, independent of `N`,
of the volume, and of the representation data.

NO CLAIM. Uniformity in volume is the content of the criterion;
no continuum or Clay statement is made anywhere in this file.

FENCE (the LOC-2 seam, stated plainly): the corpus has no
polymer-gas partition-function object, no `log Z` cluster-series
object, and no abstract KS implication (a Kotecký–Preiss bound
implying analyticity of `log Z`). What is proved here is
convergence of the per-column activity series itself
(`clusterSum ≤ 1` inside the radius). LOC-3's price for closing
the seam: (i) a `Z_polymer` object over a layer, (ii) a bridge
theorem identifying the logarithm of the layer weight with the
polymer sum, (iii) the KS implication brick transporting this
criterion to analyticity of that logarithm.
-/

namespace ThetLogos

open Finset MeasureTheory

noncomputable section

section PolymerConvergence

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- Site adjacency at the function level: equal, or joined by one
coordinate shift by `±1` in one coordinate. (The `LayerSite`
constraints on both ends do the geometric work; shifts in the
time coordinate simply never land on another layer site unless
they are trivial, so including all four coordinates only makes
the adjacency more generous — and the counting bounds safer.) -/
def siteAdj (c c' : LayerSite N) : Prop :=
  c = c' ∨ ∃ i : Fin 4,
    c'.1 = Function.update c.1 i (c.1 i + 1) ∨
    c'.1 = Function.update c.1 i (c.1 i + -1)

theorem siteAdj_flip {c c' : LayerSite N} {i : Fin 4} {ε δ : ZMod N}
    (h : c'.1 = Function.update c.1 i (c.1 i + ε)) (hεδ : ε + δ = 0) :
    c.1 = Function.update c'.1 i (c'.1 i + δ) := by
  funext j
  have hjj := congrFun h j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self] at hjj
    rw [Function.update_self, hjj, add_assoc, hεδ, add_zero]
  · rw [Function.update_of_ne hj] at hjj
    rw [Function.update_of_ne hj]
    exact hjj.symm

theorem siteAdj_symm : Symmetric (siteAdj (N := N)) := by
  intro c c' h
  rcases h with rfl | ⟨i, h | h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, Or.inr (siteAdj_flip h (by simp))⟩
  · exact Or.inr ⟨i, Or.inl (siteAdj_flip h (by simp))⟩

/-- Column adjacency: distinct columns whose base sites are
equal or joined by one spatial shift — the LOC-0 adjacency,
stated generously (any coordinate shift), which only enlarges
the connected species and hence strengthens the counting
burden the animal bound must carry. -/
def colAdj (P Q : LayerColumn N) : Prop :=
  P ≠ Q ∧ siteAdj P.1 Q.1

/-- The column graph. -/
def colGraph : SimpleGraph (LayerColumn N) where
  Adj := colAdj (N := N)
  symm := ⟨by
    intro P Q h
    exact ⟨fun hh => h.1 hh.symm, siteAdj_symm h.2⟩⟩
  loopless := ⟨fun P h => h.1 rfl⟩

/-- The function-level neighborhood of a site function: itself,
and all one-coordinate `±1` updates. At most `9` functions. -/
def funcNbhd (f : Fin 4 → ZMod N) : Finset (Fin 4 → ZMod N) :=
  insert f ((Finset.univ ×ˢ {1, -1}).image
    (fun p : Fin 4 × ZMod N => Function.update f p.1 (f p.1 + p.2)))

theorem card_funcNbhd_le (f : Fin 4 → ZMod N) :
    (funcNbhd f).card ≤ 9 := by
  refine (Finset.card_insert_le _ _).trans ?_
  refine (add_le_add_left (Finset.card_image_le.trans ?_) 1)
  rw [Finset.card_product]
  have h2 : ({1, -1} : Finset (ZMod N)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  simp only [Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_left 4 h2

/-- The columns whose site function lies in `funcNbhd P.1`,
with an arbitrary default column outside the layer. At most
`27` columns; this is the explicit envelope for the neighbor
set of `P`. -/
def colEnvelope (P : LayerColumn N) : Finset (LayerColumn N) :=
  (funcNbhd P.1.1 ×ˢ Finset.univ).image
    (fun q : (Fin 4 → ZMod N) × {ν : Fin 4 // ν ≠ 0} =>
      if h : (q.1 0).val = 0 then (⟨q.1, h⟩, q.2) else P)

theorem card_colEnvelope_le (P : LayerColumn N) :
    (colEnvelope P).card ≤ 27 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product]
  have h3 : (Finset.univ : Finset {ν : Fin 4 // ν ≠ 0}).card ≤ 3 := by
    decide
  exact Nat.mul_le_mul (card_funcNbhd_le _) h3

theorem mem_colEnvelope_self (P : LayerColumn N) :
    P ∈ colEnvelope P := by
  refine Finset.mem_image.mpr ⟨⟨P.1.1, P.2⟩, ?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    exact Finset.mem_insert_self _ _
  · rw [dif_pos P.1.2]
    rfl

/-- The neighbor set of a column, as a plain filtered finset. -/
def colNbhd (P : LayerColumn N) : Finset (LayerColumn N) := by
  classical
  exact Finset.univ.filter (colAdj P)

theorem mem_colNbhd {P Q : LayerColumn N} :
    Q ∈ colNbhd P ↔ colAdj P Q := by
  classical
  simp [colNbhd]

theorem colNbhd_subset_envelope (P : LayerColumn N) :
    colNbhd P ⊆ colEnvelope P := by
  intro Q hQ
  rw [mem_colNbhd] at hQ
  refine Finset.mem_image.mpr ⟨⟨Q.1.1, Q.2⟩, ?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rcases hQ.2 with h | ⟨i, h | h⟩
    · rw [← h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨⟨i, 1⟩, Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp⟩, h.symm⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨⟨i, -1⟩, Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp⟩, h.symm⟩)
  · rw [dif_pos Q.1.2]
    rfl

/-- **Degree bound (owned geometry).** Every column has at
most `26` neighbors in `colGraph`, uniformly in `N`: the
envelope has at most `27` columns and a column is never its
own neighbor. -/
theorem colNbhd_card_le (P : LayerColumn N) :
    (colNbhd P).card ≤ 26 := by
  have hsub : colNbhd P ⊆ (colEnvelope P).erase P := by
    intro Q hQ
    have hAdj : colAdj P Q := mem_colNbhd.mp hQ
    exact Finset.mem_erase.mpr
      ⟨fun hh => hAdj.1 hh.symm, colNbhd_subset_envelope P hQ⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (mem_colEnvelope_self P)]
  have := card_colEnvelope_le P
  omega

/-- **The polymer species.** A connected column-support of
size `≥ 3` (LOC-1: connected activities at two columns vanish
identically, so the connected species starts at three), with
a non-vacuum degree label at each of its columns. -/
structure Polymer where
  support : Finset (LayerColumn N)
  deg : LayerColumn N → ℕ
  deg_eq_zero : ∀ c ∉ support, deg c = 0
  deg_pos : ∀ c ∈ support, 1 ≤ deg c
  card_ge : 3 ≤ support.card
  connected : (colGraph.induce (support : Set (LayerColumn N))).Connected

/-- The polymer's activity: the product of LOC-1's
single-column activities over its support. (By
`colActivity_independent` the factors do not depend on the
column or on the boundary links; the product is nevertheless
taken at the polymer's own columns.) -/
noncomputable def polymerActivity (β : ℝ) (u u' : LayerLink N → G)
    (p : Polymer (N := N)) : ℝ :=
  ∏ c ∈ p.support, colActivity ρ μG β (p.deg c) u u' c

/-- The landed LOC-1 majorant, polymerwise. -/
theorem polymerActivity_majorant (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (p : Polymer (N := N)) :
    |polymerActivity ρ μG β u u' p|
      ≤ ∏ c ∈ p.support, (2 * |β|) ^ (p.deg c)
          / ((Nat.factorial (p.deg c) : ℝ)) := by
  rw [polymerActivity, Finset.abs_prod]
  have h1 : ∀ c ∈ p.support, 0 ≤ |colActivity ρ μG β (p.deg c) u u' c| :=
    fun c _ => abs_nonneg _
  have h2 : ∀ c ∈ p.support, |colActivity ρ μG β (p.deg c) u u' c|
      ≤ (2 * |β|) ^ (p.deg c) / ((Nat.factorial (p.deg c) : ℝ)) :=
    fun c _ => abs_colActivity_le ρ μG hN hρcont β (p.deg c) u u' c
  exact Finset.prod_le_prod₀ h1 h2

/-- The one-column degree majorant function: `h 0 = 0` (the
vacuum label carries no activity), `h j = (2|β|)ʲ/j!` for
`j ≥ 1`. -/
noncomputable def degMajorant (β : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else (2 * |β|) ^ j / ((Nat.factorial j : ℝ))

theorem degMajorant_nonneg (β : ℝ) (j : ℕ) :
    0 ≤ degMajorant β j := by
  by_cases hj : j = 0
  · simp [degMajorant, hj]
  · simp only [degMajorant, hj, ite_false]
    positivity

theorem degMajorant_summable (β : ℝ) :
    Summable (degMajorant β) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial (2 * |β|)) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (degMajorant_nonneg β j)]
  by_cases hj : j = 0
  · simp [degMajorant, hj]
  · simp [degMajorant, hj]

/-- The total degree majorant: `∑' j, h j = exp (2|β|) − 1`. -/
theorem tsum_degMajorant (β : ℝ) :
    ∑' j, degMajorant β j = Real.exp (2 * |β|) - 1 := by
  have hsumm := Real.summable_pow_div_factorial (2 * |β|)
  have hsplit := hsumm.sum_add_tsum_nat_add 1
  have h0 : ∑ i ∈ Finset.range 1,
        (2 * |β|) ^ i / ((Nat.factorial i : ℝ)) = 1 := by simp
  have hexp : (∑' i, (2 * |β|) ^ i / ((Nat.factorial i : ℝ)))
      = Real.exp (2 * |β|) := by
    have h1 : Real.exp (2 * |β|) = NormedSpace.exp (2 * |β|) :=
      congrFun Real.exp_eq_exp_ℝ _
    rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) (2 * |β|)]
    exact tsum_congr fun n => by
      rw [smul_eq_mul, div_eq_inv_mul, mul_comm]
  rw [h0, hexp] at hsplit
  have hdeg : ∀ j, degMajorant β (j + 1)
      = (2 * |β|) ^ (j + 1) / ((Nat.factorial (j + 1) : ℝ)) := by
    intro j
    simp [degMajorant]
  have hdeg0 : degMajorant β 0 = 0 := by simp [degMajorant]
  have hsplit2 := (degMajorant_summable β).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hdeg0, zero_add] at hsplit2
  rw [tsum_congr hdeg] at hsplit2
  linarith

theorem funcNbhd_symm {f f' : Fin 4 → ZMod N}
    (h : f' ∈ funcNbhd f) : f ∈ funcNbhd f' := by
  rw [funcNbhd, Finset.mem_insert, Finset.mem_image] at h
  rw [funcNbhd, Finset.mem_insert, Finset.mem_image]
  rcases h with rfl | ⟨p, hp, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨⟨p.1, -p.2⟩, Finset.mem_product.mpr
      ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [Finset.mem_product] at hp
      have hp2 : p.2 = 1 ∨ p.2 = -1 := by
        have h2 := hp.2
        simpa using h2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hp2 with h1 | h1 <;> simp [h1]
    · funext j
      by_cases hj : j = p.1
      · subst hj
        rw [Function.update_self, Function.update_self,
          add_assoc, add_neg_cancel, add_zero]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- The envelope relation is symmetric: the witness
construction depends only on the base site's function, and
`funcNbhd` is symmetric. -/
theorem mem_colEnvelope_symm {P Q : LayerColumn N}
    (h : Q ∈ colEnvelope P) : P ∈ colEnvelope Q := by
  obtain ⟨q, hq, hqQ⟩ := Finset.mem_image.mp h
  rw [Finset.mem_product] at hq
  by_cases hcond : (q.1 0).val = 0
  · rw [dif_pos hcond] at hqQ
    refine Finset.mem_image.mpr ⟨⟨P.1.1, P.2⟩,
      Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · have hQ1 : Q.1.1 = q.1 := by rw [← hqQ]
      rw [hQ1]
      exact funcNbhd_symm hq.1
    · rw [dif_pos P.1.2]
      rfl
  · rw [dif_neg hcond] at hqQ
    rw [← hqQ]
    exact mem_colEnvelope_self P

/-- The step graph: distinct columns whose sites lie in each
other's envelope. Walks in this graph are the encodings the
animal bound counts; every `colGraph` edge is a step, and
every step lands in the `27`-element envelope. -/
def stepGraph : SimpleGraph (LayerColumn N) where
  Adj P Q := P ≠ Q ∧ Q ∈ colEnvelope P
  symm := ⟨by
    intro P Q h
    exact ⟨fun hh => h.1 hh.symm, mem_colEnvelope_symm h.2⟩⟩
  loopless := ⟨fun P h => h.1 rfl⟩

theorem stepGraph_adj_of_colAdj {P Q : LayerColumn N}
    (h : colAdj P Q) : (stepGraph (N := N)).Adj P Q :=
  ⟨h.1, colNbhd_subset_envelope P (mem_colNbhd.mpr h)⟩

/-- The connected supports of exact size `n` through `x`. -/
def connSetsThrough (x : LayerColumn N) (n : ℕ) :
    Finset (Finset (LayerColumn N)) := by
  classical
  exact Finset.univ.filter (fun S => x ∈ S ∧ S.card = n ∧
    (colGraph.induce (S : Set (LayerColumn N))).Connected)

/-- The animal bound at constant `C`, as a named statement:
the number of connected supports of size `n` through any
fixed column is at most `C ^ n`, uniformly in everything. -/
def AnimalBound (C : ℕ) : Prop :=
  ∀ (x : LayerColumn N) (n : ℕ),
    (connSetsThrough x n).card ≤ C ^ n

/-- The shifted degree majorant is summable. -/
theorem degMajorant_summable_shift (β : ℝ) :
    Summable (fun m => degMajorant β (m + 1)) :=
  (summable_nat_add_iff 1).mpr (degMajorant_summable β)

/-- The shifted total: `∑' m, h (m+1) = exp (2|β|) − 1`. -/
theorem tsum_degMajorant_shift (β : ℝ) :
    ∑' m, degMajorant β (m + 1) = Real.exp (2 * |β|) - 1 := by
  have h := (degMajorant_summable β).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h
  have h0 : degMajorant β 0 = 0 := by simp [degMajorant]
  rw [h0, tsum_degMajorant] at h
  linarith

/-- Splitting a degree assignment on `insert c S` into the
degree at `c` and the assignment on `S`. -/
def degAssignEquiv {c : LayerColumn N} {S : Finset (LayerColumn N)}
    (hcS : c ∉ S) :
    (↥(insert c S) → ℕ) ≃ ℕ × (↥S → ℕ) where
  toFun k := (k ⟨c, Finset.mem_insert_self c S⟩,
    fun x : ↥S => k ⟨x.1, Finset.mem_insert_of_mem x.2⟩)
  invFun p := fun x : ↥(insert c S) =>
    if h : x.1 = c then p.1
    else p.2 ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left h⟩
  left_inv k := by
    funext x
    dsimp only
    by_cases hx : x.1 = c
    · rw [dif_pos hx]
      congr 1
      exact Subtype.ext hx.symm
    · rw [dif_neg hx]
  right_inv p := by
    obtain ⟨j, k'⟩ := p
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [dif_pos rfl]
    funext x
    dsimp only
    show (if h : (⟨x.1, Finset.mem_insert_of_mem x.2⟩ :
        ↥(insert c S)).1 = c then j
      else k' ⟨x.1, (Finset.mem_insert.mp
        (Finset.mem_insert_of_mem x.2)).resolve_left h⟩) = k' x
    have hne : x.1 ≠ c := fun h => hcS (h ▸ x.2)
    rw [dif_neg hne]

/-- The split assignment's degree at the inserted column. -/
theorem degAssignEquiv_symm_fst {c : LayerColumn N}
    {S : Finset (LayerColumn N)} (hcS : c ∉ S) (j : ℕ)
    (k' : ↥S → ℕ) :
    (degAssignEquiv hcS).symm (j, k')
      ⟨c, Finset.mem_insert_self c S⟩ = j :=
  dif_pos rfl

/-- The split assignment's degree at a column of `S`. -/
theorem degAssignEquiv_symm_of_mem {c : LayerColumn N}
    {S : Finset (LayerColumn N)} (hcS : c ∉ S) (j : ℕ)
    (k' : ↥S → ℕ) (y : LayerColumn N) (hy : y ∈ S) :
    (degAssignEquiv hcS).symm (j, k')
      ⟨y, Finset.mem_insert_of_mem hy⟩ = k' ⟨y, hy⟩ := by
  have hne : y ≠ c := fun h => hcS (h ▸ hy)
  show (if h : y = c then j
    else k' ⟨y, (Finset.mem_insert.mp
      (Finset.mem_insert_of_mem hy)).resolve_left h⟩) = k' ⟨y, hy⟩
  rw [dif_neg hne]

/-- The degree product over `insert c S`, split along
`degAssignEquiv`: the factor at `c` times the product
over `S`. -/
theorem degProd_split {c : LayerColumn N}
    {S : Finset (LayerColumn N)} (hcS : c ∉ S) (β : ℝ)
    (j : ℕ) (k' : ↥S → ℕ) :
    ∏ x : ↥(insert c S), degMajorant β
        ((degAssignEquiv hcS).symm (j, k') x + 1)
      = degMajorant β (j + 1)
        * ∏ x : ↥S, degMajorant β (k' x + 1) := by
  classical
  set e := (degAssignEquiv hcS).symm (j, k') with he
  set G' : LayerColumn N → ℝ := fun y =>
    if hy : y ∈ insert c S then degMajorant β (e ⟨y, hy⟩ + 1)
    else 1 with hG'
  have hGc : G' c = degMajorant β (j + 1) := by
    show (if hy : c ∈ insert c S then degMajorant β (e ⟨c, hy⟩ + 1)
      else 1) = degMajorant β (j + 1)
    rw [dif_pos (Finset.mem_insert_self c S), he,
      degAssignEquiv_symm_fst hcS j k']
  have hGS : ∀ x : ↥S, G' x.1 = degMajorant β (k' x + 1) := by
    intro x
    show (if hy : x.1 ∈ insert c S then
        degMajorant β (e ⟨x.1, hy⟩ + 1) else 1)
      = degMajorant β (k' x + 1)
    rw [dif_pos (Finset.mem_insert_of_mem x.2), he,
      degAssignEquiv_symm_of_mem hcS j k' x.1 x.2]
  have hGtop : ∀ x : ↥(insert c S),
      G' x.1 = degMajorant β (e x + 1) := by
    intro x
    show (if hy : x.1 ∈ insert c S then
        degMajorant β (e ⟨x.1, hy⟩ + 1) else 1)
      = degMajorant β (e x + 1)
    rw [dif_pos x.2]
  calc ∏ x : ↥(insert c S), degMajorant β (e x + 1)
      = ∏ x : ↥(insert c S), G' x.1 :=
        Finset.prod_congr rfl fun x _ => (hGtop x).symm
    _ = ∏ y ∈ insert c S, G' y := by
        rw [← Finset.prod_attach (insert c S) G',
          Finset.univ_eq_attach]
    _ = G' c * ∏ y ∈ S, G' y := Finset.prod_insert hcS
    _ = degMajorant β (j + 1)
          * ∏ x : ↥S, degMajorant β (k' x + 1) := by
        rw [hGc, ← Finset.prod_attach S G', Finset.univ_eq_attach]
        congr 1
        exact Finset.prod_congr rfl fun x _ => hGS x

/-- **The per-support degree sum.** The degree-majorant
product over a support `S` sums to
`(exp (2|β|) − 1) ^ |S|`: the pi-type sum factors as a
product of one-column sums, each `exp (2|β|) − 1` by
`tsum_degMajorant_shift`. -/
theorem degProd_hasSum (β : ℝ) (S : Finset (LayerColumn N)) :
    HasSum (fun k : ↥S → ℕ => ∏ x : ↥S, degMajorant β (k x + 1))
      ((Real.exp (2 * |β|) - 1) ^ S.card) := by
  classical
  induction S using Finset.induction with
  | empty =>
    have hU : Unique (↥(∅ : Finset (LayerColumn N)) → ℕ) :=
      ⟨⟨fun _ => 0⟩, fun k => funext fun x =>
        (Finset.notMem_empty x.1 x.2).elim⟩
    haveI := hU
    have h := hasSum_unique
      (fun k : (↥(∅ : Finset (LayerColumn N)) → ℕ) =>
        ∏ x : ↥(∅ : Finset (LayerColumn N)),
          degMajorant β (k x + 1))
    simpa using h
  | @insert c S hcS ih =>
    have hA : HasSum (fun j => degMajorant β (j + 1))
        (Real.exp (2 * |β|) - 1) := by
      have h := (degMajorant_summable_shift β).hasSum
      rwa [tsum_degMajorant_shift] at h
    have h1 : ∀ j : ℕ, Summable (fun k' : ↥S → ℕ =>
        degMajorant β (j + 1)
          * ∏ x : ↥S, degMajorant β (k' x + 1)) :=
      fun j => ih.summable.mul_left (degMajorant β (j + 1))
    have h2 : Summable (fun j : ℕ => ∑' k' : ↥S → ℕ,
        degMajorant β (j + 1)
          * ∏ x : ↥S, degMajorant β (k' x + 1)) := by
      have hsum : ∀ j : ℕ, (∑' k' : ↥S → ℕ,
          degMajorant β (j + 1)
            * ∏ x : ↥S, degMajorant β (k' x + 1))
          = degMajorant β (j + 1)
            * (Real.exp (2 * |β|) - 1) ^ S.card := by
        intro j
        rw [ih.summable.tsum_mul_left (degMajorant β (j + 1))]
        exact congrArg _ ih.tsum_eq
      simp_rw [hsum]
      exact (degMajorant_summable_shift β).mul_right _
    have hprod : Summable (fun p : ℕ × (↥S → ℕ) =>
        degMajorant β (p.1 + 1)
          * ∏ x : ↥S, degMajorant β (p.2 x + 1)) :=
      (summable_prod_of_nonneg (f := fun p : ℕ × (↥S → ℕ) =>
        degMajorant β (p.1 + 1)
          * ∏ x : ↥S, degMajorant β (p.2 x + 1))
        (fun p => mul_nonneg (degMajorant_nonneg β _)
          (Finset.prod_nonneg fun x _ =>
            degMajorant_nonneg β _))).mpr ⟨h1, h2⟩
    have hHas : HasSum (fun p : ℕ × (↥S → ℕ) =>
        degMajorant β (p.1 + 1)
          * ∏ x : ↥S, degMajorant β (p.2 x + 1))
        ((Real.exp (2 * |β|) - 1)
          * (Real.exp (2 * |β|) - 1) ^ S.card) := by
      have h := hprod.hasSum
      rw [← Summable.tsum_mul_tsum hA.summable ih.summable hprod,
        tsum_degMajorant_shift, ih.tsum_eq] at h
      exact h
    have hfun : (fun k : ↥(insert c S) → ℕ =>
        ∏ x : ↥(insert c S), degMajorant β (k x + 1))
        = (fun p : ℕ × (↥S → ℕ) => degMajorant β (p.1 + 1)
            * ∏ x : ↥S, degMajorant β (p.2 x + 1))
          ∘ (degAssignEquiv hcS) := by
      funext k
      show ∏ x : ↥(insert c S), degMajorant β (k x + 1)
        = degMajorant β (((degAssignEquiv hcS) k).1 + 1)
          * ∏ x : ↥S, degMajorant β
              (((degAssignEquiv hcS) k).2 x + 1)
      rw [← degProd_split hcS β ((degAssignEquiv hcS) k).1
        ((degAssignEquiv hcS) k).2]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [Prod.mk.eta, Equiv.symm_apply_apply]
    have hcard : (insert c S).card = S.card + 1 :=
      Finset.card_insert_of_notMem hcS
    rw [hfun, hcard, pow_succ']
    exact (degAssignEquiv hcS).hasSum_iff.mpr hHas

theorem degMajorant_succ (β : ℝ) (j : ℕ) :
    degMajorant β (j + 1)
      = (2 * |β|) ^ (j + 1) / ((Nat.factorial (j + 1) : ℝ)) := by
  simp [degMajorant]

/-- The support activity over degree assignments
`j : ↥S → ℕ`, where column `x` carries the non-vacuum
degree `j x + 1` (a polymer's `deg − 1`). -/
noncomputable def supportActivity (β : ℝ) (u u' : LayerLink N → G)
    (S : Finset (LayerColumn N)) (j : ↥S → ℕ) : ℝ :=
  ∏ x : ↥S, colActivity ρ μG β (j x + 1) u u' x.1

/-- The per-support degree sum of the activity is at most
`(exp (2|β|) − 1) ^ |S|`, by LOC-1's majorant summed
through `degProd_hasSum`. -/
theorem supportActivity_tsum_abs_le (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G)
    (S : Finset (LayerColumn N)) :
    ∑' j : ↥S → ℕ, |supportActivity ρ μG β u u' S j|
      ≤ (Real.exp (2 * |β|) - 1) ^ S.card := by
  have hterm : ∀ j : ↥S → ℕ,
      |supportActivity ρ μG β u u' S j|
        ≤ ∏ x : ↥S, degMajorant β (j x + 1) := by
    intro j
    rw [supportActivity, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun x _ => abs_nonneg _)
      fun x _ => ?_
    rw [degMajorant_succ]
    exact abs_colActivity_le ρ μG hN hρcont β (j x + 1) u u' x.1
  have hsumm := (degProd_hasSum β S).summable
  have hsumm2 : Summable (fun j : ↥S → ℕ =>
      |supportActivity ρ μG β u u' S j|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hterm hsumm
  calc ∑' j : ↥S → ℕ, |supportActivity ρ μG β u u' S j|
      ≤ ∑' j : ↥S → ℕ, ∏ x : ↥S, degMajorant β (j x + 1) :=
        hsumm2.tsum_le_of_sum_le fun T =>
          (Finset.sum_le_sum fun j _ => hterm j).trans
            (hsumm.sum_le_tsum T (fun j _ =>
              Finset.prod_nonneg fun x _ => degMajorant_nonneg β _))
    _ = (Real.exp (2 * |β|) - 1) ^ S.card :=
        (degProd_hasSum β S).tsum_eq

/-- **The explicit Kotecky–Preiss radius.**
`β₀ = (1/2)·ln(1 + 1/(2·729·e))`: at `|β| < β₀` the
per-column weight `w = exp (2|β|) − 1` satisfies
`729·e·w < 1/2`. It depends on nothing — no `N`, no
volume, no representation data. -/
noncomputable def beta0 : ℝ :=
  (1 / 2) * Real.log (1 + 1 / (2 * 729 * Real.exp 1))

theorem beta0_pos : 0 < beta0 := by
  have h1 : (1:ℝ) < 1 + 1 / (2 * 729 * Real.exp 1) := by
    have hpos : (0:ℝ) < 1 / (2 * 729 * Real.exp 1) := by
      positivity
    linarith
  show (0:ℝ) < (1 / 2) * Real.log _
  exact mul_pos (by norm_num) (Real.log_pos h1)

/-- The weight estimate at the radius: with
`q = 729 · (e · w)`, `|β| < β₀` gives `q < 1/2`. -/
theorem cluster_weight_lt (β : ℝ) (hβ : |β| < beta0) :
    729 * (Real.exp 1 * (Real.exp (2 * |β|) - 1)) < 1 / 2 := by
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hne : Real.exp 1 ≠ 0 := ne_of_gt he
  have h2β : 2 * |β|
      < Real.log (1 + 1 / (2 * 729 * Real.exp 1)) := by
    have h : |β| < (1 / 2)
        * Real.log (1 + 1 / (2 * 729 * Real.exp 1)) := hβ
    linarith
  have hX : (0:ℝ) < 1 + 1 / (2 * 729 * Real.exp 1) := by
    have hpos : (0:ℝ) < 1 / (2 * 729 * Real.exp 1) := by
      positivity
    linarith
  have hexp : Real.exp (2 * |β|)
      < 1 + 1 / (2 * 729 * Real.exp 1) := by
    rw [← Real.exp_log hX]
    exact Real.exp_lt_exp.mpr h2β
  have hw : Real.exp (2 * |β|) - 1
      < 1 / (2 * 729 * Real.exp 1) := by linarith
  calc 729 * (Real.exp 1 * (Real.exp (2 * |β|) - 1))
      < 729 * (Real.exp 1 * (1 / (2 * 729 * Real.exp 1))) :=
        mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_left hw he) (by norm_num)
    _ = 1 / 2 := by
        have hne2 : (2:ℝ) * 729 * Real.exp 1 ≠ 0 := by positivity
        field_simp

/-- All connected supports through `x` (any size `≥ 3`). -/
def connSupportsThrough (x : LayerColumn N) :
    Finset (Finset (LayerColumn N)) := by
  classical
  exact Finset.univ.filter (fun S => x ∈ S ∧ 3 ≤ S.card ∧
    (colGraph.induce (S : Set (LayerColumn N))).Connected)

/-- The per-column cluster sum: over all connected
supports through `x`, the Kotecky–Preiss weight
`exp |S|` times the total absolute activity. -/
noncomputable def clusterSum (β : ℝ) (u u' : LayerLink N → G)
    (x : LayerColumn N) : ℝ :=
  ∑ S ∈ connSupportsThrough (N := N) x, Real.exp (S.card : ℝ) *
    ∑' j : ↥S → ℕ, |supportActivity ρ μG β u u' S j|

theorem exp_card_eq (n : ℕ) :
    Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
  simpa using Real.exp_nat_mul (1 : ℝ) n

/-- **The Kotecky–Preiss criterion (conditional on the
animal bound).** If connected supports of size `n`
through a column number at most `729 ^ n`, then for
`|β| < β₀` the per-column cluster sum is at most `1` —
with `β₀` and every constant independent of `N`, of the
volume, and of the representation data. -/
theorem ks_criterion (hAnimal : AnimalBound (N := N) 729)
    (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (hβ : |β| < beta0) (u u' : LayerLink N → G)
    (x : LayerColumn N) :
    clusterSum ρ μG β u u' x ≤ 1 := by
  classical
  set w : ℝ := Real.exp (2 * |β|) - 1 with hw
  set r : ℝ := Real.exp 1 * w with hr
  set q : ℝ := 729 * r with hq
  have hw0 : 0 ≤ w := by
    have h := Real.exp_le_exp.mpr
      (show (0:ℝ) ≤ 2 * |β| by positivity)
    rw [Real.exp_zero] at h
    simp only [hw]
    linarith
  have hr0 : 0 ≤ r := mul_nonneg (Real.exp_pos 1).le hw0
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact mul_nonneg (by norm_num) hr0
  have hq12 : q < 1 / 2 := cluster_weight_lt β hβ
  have hterm : ∀ S ∈ connSupportsThrough (N := N) x,
      Real.exp (S.card : ℝ) * ∑' j : ↥S → ℕ,
          |supportActivity ρ μG β u u' S j|
        ≤ r ^ S.card := by
    intro S _
    have h1 := supportActivity_tsum_abs_le ρ μG hN hρcont β u u' S
    have h2 : Real.exp (S.card : ℝ)
          * ∑' j : ↥S → ℕ, |supportActivity ρ μG β u u' S j|
        ≤ Real.exp (S.card : ℝ)
          * (Real.exp (2 * |β|) - 1) ^ S.card :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    refine h2.trans_eq ?_
    rw [exp_card_eq, ← hw, ← mul_pow, ← hr]
  have hM : ∀ S ∈ connSupportsThrough (N := N) x,
      S.card ∈ Finset.Ico 3 (Fintype.card (LayerColumn N) + 1) := by
    intro S hS
    obtain ⟨-, -, h3, -⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_Ico.mpr ⟨h3, ?_⟩
    have hle := Finset.card_le_univ S
    omega
  have hfiber : ∀ n : ℕ, 3 ≤ n →
      (connSupportsThrough (N := N) x).filter
          (fun S => S.card = n)
        = connSetsThrough (N := N) x n := by
    intro n hn
    ext S
    simp only [connSupportsThrough, connSetsThrough,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hx, -, hconn⟩, hcard⟩
      exact ⟨hx, hcard, hconn⟩
    · rintro ⟨hx, hcard, hconn⟩
      exact ⟨⟨hx, by omega, hconn⟩, hcard⟩
  have hsum2 : clusterSum ρ μG β u u' x
      ≤ ∑ n ∈ Finset.Ico 3 (Fintype.card (LayerColumn N) + 1),
          q ^ n := by
    calc clusterSum ρ μG β u u' x
        = ∑ S ∈ connSupportsThrough (N := N) x,
            Real.exp (S.card : ℝ) * ∑' j : ↥S → ℕ,
              |supportActivity ρ μG β u u' S j| := rfl
      _ ≤ ∑ S ∈ connSupportsThrough (N := N) x, r ^ S.card :=
          Finset.sum_le_sum hterm
      _ = ∑ n ∈ Finset.Ico 3 (Fintype.card (LayerColumn N) + 1),
            ∑ S ∈ connSetsThrough (N := N) x n, r ^ S.card := by
          rw [← Finset.sum_fiberwise_of_maps_to hM
            (fun S : Finset (LayerColumn N) => r ^ S.card)]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_Ico] at hn
          rw [hfiber n hn.1]
      _ ≤ ∑ n ∈ Finset.Ico 3 (Fintype.card (LayerColumn N) + 1),
            q ^ n := by
          refine Finset.sum_le_sum fun n _ => ?_
          calc ∑ S ∈ connSetsThrough (N := N) x n, r ^ S.card
              = ∑ S ∈ connSetsThrough (N := N) x n, r ^ n :=
                Finset.sum_congr rfl fun S hS => by
                  obtain ⟨-, -, hcard, -⟩ := Finset.mem_filter.mp hS
                  rw [hcard]
            _ = (connSetsThrough (N := N) x n).card * r ^ n := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 729 ^ n * r ^ n :=
                mul_le_mul_of_nonneg_right
                  (by exact_mod_cast hAnimal x n)
                  (pow_nonneg hr0 n)
            _ = q ^ n := by
                rw [hq]
                exact (mul_pow 729 r n).symm
  have htail : ∑ n ∈ Finset.Ico 3
        (Fintype.card (LayerColumn N) + 1), q ^ n ≤ 1 := by
    have hq1 : q < 1 := hq12.trans (by norm_num)
    have hgeo : Summable (fun n : ℕ => q ^ n) :=
      summable_geometric_of_lt_one hq0 hq1
    have hshift : Summable (fun n : ℕ => q ^ (n + 3)) :=
      (summable_nat_add_iff 3).mpr hgeo
    have htsum : ∑' n : ℕ, q ^ (n + 3) = q ^ 3 * (1 - q)⁻¹ := by
      have hfun : (fun n : ℕ => q ^ (n + 3))
          = fun n => q ^ 3 * q ^ n := by
        funext n
        rw [pow_add, mul_comm]
      rw [hfun, tsum_mul_left,
        tsum_geometric_of_lt_one hq0 hq1]
    have hle : ∑ n ∈ Finset.Ico 3
          (Fintype.card (LayerColumn N) + 1), q ^ n
        ≤ ∑' n : ℕ, q ^ (n + 3) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hcong : ∑ i ∈ Finset.range
            (Fintype.card (LayerColumn N) + 1 - 3), q ^ (3 + i)
          = ∑ i ∈ Finset.range
            (Fintype.card (LayerColumn N) + 1 - 3), q ^ (i + 3) :=
        Finset.sum_congr rfl fun i _ => by rw [add_comm]
      rw [hcong]
      exact hshift.sum_le_tsum _ (fun i _ => pow_nonneg hq0 _)
    refine hle.trans ?_
    rw [htsum, ← div_eq_mul_inv]
    refine (div_le_one (by linarith [hq12] :
      (0:ℝ) < 1 - q)).mpr ?_
    have hq2 : q ^ 2 ≤ 1 / 4 := by
      rw [pow_two]
      have h := mul_le_mul hq12.le hq12.le hq0
        (show (0:ℝ) ≤ 1 / 2 by norm_num)
      norm_num at h
      exact h
    have hq3 : q ^ 3 ≤ 1 / 8 := by
      calc q ^ 3 = q ^ 2 * q := by rw [pow_succ]
        _ ≤ (1 / 4) * (1 / 2) :=
            mul_le_mul hq2 hq12.le hq0 (by norm_num)
        _ = 1 / 8 := by norm_num
    linarith
  exact hsum2.trans htail

/-- The step graph on a finite column type is locally finite. -/
instance stepGraph_locallyFinite :
    SimpleGraph.LocallyFinite (stepGraph (N := N)) :=
  fun _ => Fintype.ofFinite _

/-- The number of neighbor steps available at any column is at most
`27`: the step-graph neighborhood sits inside the envelope. -/
theorem stepGraph_neighbor_card_le (x : LayerColumn N) :
    (stepGraph (N := N)).neighborFinset x ⊆ colEnvelope x := by
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw
  exact hw.2

/-- Counting closed step-walks: the number of `stepGraph` walks of
length `m` between fixed endpoints is at most `27 ^ m`, by induction
on the recursive definition of `finsetWalkLength` (each step chooses
a neighbor inside an envelope of at most `27` columns). -/
theorem stepWalk_card_le (m : ℕ) (x y : LayerColumn N) :
    ((stepGraph (N := N)).finsetWalkLength m x y).card ≤ 27 ^ m := by
  induction m generalizing x y with
  | zero =>
      by_cases h : x = y
      · subst h
        simp [SimpleGraph.finsetWalkLength]
      · simp [SimpleGraph.finsetWalkLength, h]
  | succ m ih =>
      rw [SimpleGraph.finsetWalkLength]
      refine (Finset.card_biUnion_le).trans ?_
      have hterm : ∀ w : ↥((stepGraph (N := N)).neighborSet x),
          (((stepGraph (N := N)).finsetWalkLength m w y).map
            ⟨fun p => SimpleGraph.Walk.cons w.property p,
              by intro a b h; injection h⟩).card ≤ 27 ^ m := by
        intro w
        rw [Finset.card_map]
        exact ih w.1 y
      have hcard : (Finset.univ : Finset ↥((stepGraph (N := N)).neighborSet x)).card
          ≤ 27 := by
        have h1 : Fintype.card ↥((stepGraph (N := N)).neighborSet x)
            = ((stepGraph (N := N)).neighborSet x).ncard :=
          Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq _)
        have h2 : ((stepGraph (N := N)).neighborSet x).ncard
            ≤ ((colEnvelope x : Finset (LayerColumn N)) : Set (LayerColumn N)).ncard := by
          apply Set.ncard_le_ncard _ (Set.toFinite _)
          intro w hw
          rw [SimpleGraph.mem_neighborSet] at hw
          exact hw.2
        rw [Finset.card_univ, h1]
        refine h2.trans ?_
        rw [Set.ncard_coe_finset]
        exact card_colEnvelope_le (N := N) x
      calc ∑ w ∈ (Finset.univ : Finset ↥((stepGraph (N := N)).neighborSet x)),
              (((stepGraph (N := N)).finsetWalkLength m w y).map
                ⟨fun p => SimpleGraph.Walk.cons w.property p,
                  by intro a b h; injection h⟩).card
          ≤ ∑ _w ∈ (Finset.univ : Finset ↥((stepGraph (N := N)).neighborSet x)),
              27 ^ m := Finset.sum_le_sum fun w _ => hterm w
        _ = (Finset.univ : Finset ↥((stepGraph (N := N)).neighborSet x)).card
              * 27 ^ m := by rw [Finset.sum_const, nsmul_eq_mul]; norm_num
        _ ≤ 27 * 27 ^ m := Nat.mul_le_mul_right _ hcard
        _ = 27 ^ (m + 1) := by rw [pow_succ, mul_comm]

/-- Detour insertion: a closed step-walk through `u` can be enlarged
by a round trip `u → z → u` along a step edge, adding exactly the
vertex `z` to the support and exactly `2` to the length. -/
theorem exists_closed_walk_insert (x : LayerColumn N)
    (W : (stepGraph (N := N)).Walk x x) {u z : LayerColumn N}
    (hu : u ∈ W.support) (h : (stepGraph (N := N)).Adj u z) :
    ∃ W' : (stepGraph (N := N)).Walk x x,
      W'.support.toFinset = insert z W.support.toFinset
        ∧ W'.length = W.length + 2 := by
  obtain ⟨W₁, W₂, hW⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_append.mp hu
  refine ⟨W₁.append ((SimpleGraph.Walk.cons h
    (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil)).append W₂), ?_, ?_⟩
  · have hu12 : u ∈ W₁.support ∨ u ∈ W₂.support := by
      rw [← SimpleGraph.Walk.mem_support_append_iff, ← hW]
      exact hu
    have hW' : insert z W.support.toFinset
        = insert z (W₁.append W₂).support.toFinset := by rw [hW]
    rw [hW']
    ext a
    simp only [List.mem_toFinset, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      Finset.mem_insert]
    constructor
    · rintro (h1 | (rfl | rfl | rfl) | h3)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr hu12
      · exact Or.inl rfl
      · exact Or.inr hu12
      · exact Or.inr (Or.inr h3)
    · rintro (rfl | h1 | h3)
      · exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
      · exact Or.inl h1
      · exact Or.inr (Or.inr h3)
  · rw [hW, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_append]
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
    omega

/-- Removable vertex: in a connected induced subgraph on at least two
columns, some column `z` can be erased while keeping the induced
subgraph connected, and `z` has a `colGraph` neighbor inside the
remainder. Built on Mathlib's finite removable-vertex lemma,
transported along the canonical identification of
`(colGraph.induce S).induce {v}ᶜ` with `colGraph.induce (S.erase v)`. -/
theorem exists_removable (S : Finset (LayerColumn N)) (x : LayerColumn N)
    (hx : x ∈ S) (hconn : (colGraph.induce (S : Set (LayerColumn N))).Connected) (hcard : 2 ≤ S.card) :
    ∃ z ∈ S, (colGraph.induce ((S.erase z) : Set (LayerColumn N))).Connected
      ∧ ∃ u ∈ S.erase z, colGraph.Adj u z := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  haveI : Nontrivial ↥S :=
    ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
  obtain ⟨v, hvconn⟩ :=
    hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  -- transport the connectedness along the canonical vertex equiv
  let e : ↥((S.erase v.1 : Finset (LayerColumn N)) : Set (LayerColumn N)) ≃
      ↥({v}ᶜ : Set ↥(S : Set (LayerColumn N))) :=
    { toFun := fun p => ⟨⟨p.1,
        (Finset.mem_erase.mp (Finset.mem_coe.mp p.2)).2⟩, by
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun h => (Finset.mem_erase.mp (Finset.mem_coe.mp p.2)).1
          (congrArg Subtype.val h)⟩
      invFun := fun q => ⟨q.1.1, Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨fun h => q.2 (by
          rw [Set.mem_singleton_iff]
          exact Subtype.ext h), Finset.mem_coe.mp q.1.2⟩)⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun q => Subtype.ext rfl }
  let iso : (colGraph.induce ((S.erase v.1) : Set (LayerColumn N))) ≃g
      ((colGraph.induce (S : Set (LayerColumn N))).induce {v}ᶜ) :=
    ⟨e, by
      intro p q
      show colGraph.Adj p.1 q.1 ↔ colGraph.Adj p.1 q.1
      exact Iff.rfl⟩
  have hconn' : (colGraph.induce ((S.erase v.1) : Set (LayerColumn N))).Connected :=
    iso.connected_iff.mpr hvconn
  refine ⟨v.1, Finset.mem_coe.mp v.2, hconn', ?_⟩
  -- a neighbor of `v` inside the remainder, since `v` is not isolated
  have hniso := hconn.preconnected.not_isIsolated v
  obtain ⟨u, huadj⟩ : ∃ u, (colGraph.induce (S : Set (LayerColumn N))).Adj v u := by
    by_contra hc
    push_neg at hc
    exact hniso hc
  have huadj' : colGraph.Adj v.1 u.1 := SimpleGraph.induce_adj.mp huadj
  refine ⟨u.1, Finset.mem_erase.mpr ⟨fun h => ?_,
    Finset.mem_coe.mp u.2⟩, huadj'.symm⟩
  exact absurd (h ▸ huadj') (SimpleGraph.irrefl _)

/-- Spanning closed step-walk: every connected finite support `S`
through `x` is the support of a closed `stepGraph` walk based at `x`
of length `2 * |S| - 2`, by strong induction on `|S|`, peeling a
removable vertex each step (a round-trip detour when the peeled
vertex is not the base, a base transfer when it is). -/
theorem spanning_closed_walk : ∀ (n : ℕ) (S : Finset (LayerColumn N))
    (x : LayerColumn N), S.card = n → x ∈ S →
    (colGraph.induce (S : Set (LayerColumn N))).Connected →
    ∃ W : (stepGraph (N := N)).Walk x x,
      W.support.toFinset = S ∧ W.length = 2 * S.card - 2 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro S x hcn hx hconn
      subst hcn
      rcases Nat.lt_or_ge S.card 2 with hlt | hge
      · have hcard1 : S.card = 1 := by
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
          omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
        have hxmem : x ∈ ({a} : Finset (LayerColumn N)) := ha.symm ▸ hx
        have hax : a = x := (Finset.mem_singleton.mp hxmem).symm
        refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
        · simp [ha, hax, SimpleGraph.Walk.support_nil]
        · simp [SimpleGraph.Walk.length_nil, hcard1]
      · obtain ⟨z, hzS, hzconn, u, huS', huadj⟩ :=
          exists_removable S x hx hconn hge
        have hcard' : (S.erase z).card = S.card - 1 :=
          Finset.card_erase_of_mem hzS
        by_cases hzx : z = x
        · subst hzx
          obtain ⟨W', hsupp', hlen'⟩ := ih (S.erase z).card
            (by omega) (S.erase z) u rfl huS' hzconn
          have hstep1 : (stepGraph (N := N)).Adj z u :=
            stepGraph_adj_of_colAdj huadj.symm
          have hstep2 : (stepGraph (N := N)).Adj u z :=
            stepGraph_adj_of_colAdj huadj
          refine ⟨(SimpleGraph.Walk.cons hstep1 W').append
            (SimpleGraph.Walk.cons hstep2 SimpleGraph.Walk.nil), ?_, ?_⟩
          · ext a
            have hmem : a ∈ W'.support ↔ a ∈ S.erase z := by
              rw [← List.mem_toFinset, hsupp']
            simp only [List.mem_toFinset,
              SimpleGraph.Walk.mem_support_append_iff,
              SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
              List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
            constructor
            · rintro ((rfl | h1) | (rfl | rfl))
              · exact hzS
              · exact Finset.mem_of_mem_erase (hmem.mp h1)
              · exact Finset.mem_of_mem_erase huS'
              · exact hzS
            · intro haS
              by_cases haz : a = z
              · exact Or.inl (Or.inl haz)
              · exact Or.inl (Or.inr (hmem.mpr
                  (Finset.mem_erase.mpr ⟨haz, haS⟩)))
          · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
              SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil,
              hlen', hcard']
            omega
        · have hxS' : x ∈ S.erase z :=
            Finset.mem_erase.mpr ⟨Ne.symm hzx, hx⟩
          obtain ⟨W', hsupp', hlen'⟩ := ih (S.erase z).card
            (by omega) (S.erase z) x rfl hxS' hzconn
          have huW' : u ∈ W'.support := by
            have hmem : u ∈ W'.support.toFinset := by
              rw [hsupp']; exact huS'
            exact List.mem_toFinset.mp hmem
          obtain ⟨W'', hsupp'', hlen''⟩ := exists_closed_walk_insert x W'
            huW' (stepGraph_adj_of_colAdj huadj)
          refine ⟨W'', ?_, ?_⟩
          · rw [hsupp'', hsupp', Finset.insert_erase hzS]
          · rw [hlen'', hlen', hcard']
            omega

/-- The animal bound at `C = 729 = 27 ^ 2`, proved from the proved
envelope bound: each connected support of size `n` through `x` is
the support of a closed step-walk of length `2n - 2` at `x`, the
support map is injective, and such walks number at most
`27 ^ (2n - 2) ≤ 729 ^ n`. -/
theorem animal_bound_729 : AnimalBound (N := N) 729 := by
  classical
  intro x n
  have key : ∀ S : Finset (LayerColumn N),
      ∃ W : (stepGraph (N := N)).Walk x x,
        S ∈ connSetsThrough (N := N) x n →
          W.support.toFinset = S ∧ W.length = 2 * n - 2 := by
    intro S
    by_cases hS : S ∈ connSetsThrough (N := N) x n
    · obtain ⟨-, hxS, hcard, hconn⟩ := Finset.mem_filter.mp hS
      obtain ⟨W, h1, h2⟩ := spanning_closed_walk n S x hcard hxS hconn
      exact ⟨W, fun _ => ⟨h1, by rw [h2, hcard]⟩⟩
    · exact ⟨SimpleGraph.Walk.nil, fun h => absurd h hS⟩
  choose f hf using key
  refine (Finset.card_le_card_of_injOn
    (t := (stepGraph (N := N)).finsetWalkLength (2 * n - 2) x x) f ?_ ?_).trans ?_
  · intro S hS
    exact SimpleGraph.mem_finsetWalkLength_iff.mpr (hf S hS).2
  · intro S hS T hT hST
    have h1 := (hf S hS).1
    have h2 := (hf T hT).1
    rw [← h1, ← h2, hST]
  · refine (stepWalk_card_le (2 * n - 2) x x).trans ?_
    refine (Nat.pow_le_pow_right (by norm_num) (by omega : 2 * n - 2 ≤ 2 * n)).trans ?_
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) n

/-- The KS / Kotecký–Preiss criterion at the U(1)-style single-layer
seat, unconditional form: the animal bound is now a theorem of this
module (`animal_bound_729`), so for every even `N`, every continuous
representation datum, and every `|β| < beta0`, the per-column
cluster sum is at most `1`. -/
theorem ks_criterion_full (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (hβ : |β| < beta0) (u u' : LayerLink N → G)
    (x : LayerColumn N) :
    clusterSum ρ μG β u u' x ≤ 1 :=
  ks_criterion ρ μG animal_bound_729 hN hρcont β hβ u u' x

end PolymerConvergence

end

end ThetLogos
