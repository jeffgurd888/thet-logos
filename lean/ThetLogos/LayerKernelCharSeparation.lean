/-
# WP2 character route, Module B, brick B2a2 — the
# separation identity: a column character as a sum over
# channel tuples of separated features

For a column-type assignment `t` (a chosen irreducible
character per column) and boundary words `u, u'`, the
`μG`-average over the stratum variables `α` of the
product of the columns' characters is a sum over channel
tuples `c` of `feat c u * star (feat c u')`, where the
feature `feat` (B2a2's `charSepFeat`, built on B2a1's
chosen models) is a plain function of the boundary word:
the `α`-letters regroup by sites, the stratum sum
factorizes over sites, and each site's tensor average is
split by its channel decomposition (A2b).  The counting
factor `(card (LayerSite N → G))⁻¹` cancels exactly
against the per-site `card G` factors.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at
general finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity
object.
-/

import ThetLogos.LayerKernelCharModel
import ThetLogos.LayerKernelColumnExpansion
import ThetLogos.LayerKernelTensorChannel
import ThetLogos.LayerKernelContractionAPI

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal InnerProductSpace

namespace ThetLogos

section CharSeparation

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  [MeasurableMul G] [CompactSpace G] [LocallyCompactSpace G]
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- Columns based at a site (as the coercion of the
corresponding filter finset, so that `Finset.prod_subtype`
applies with the finset's own fintype instance). -/
abbrev siteBase (s : LayerSite N) : Type :=
  ↥(Finset.univ.filter (fun P : LayerColumn N => P.1 = s))

/-- Columns whose shift-target is a site. -/
abbrev siteShift (s : LayerSite N) : Type :=
  ↥(Finset.univ.filter (fun P : LayerColumn N =>
    layerShift P.2.1 P.2.2 P.1 = s))

/-- The slot type of a site: its base columns and its
shift-target columns. -/
abbrev siteSlot (s : LayerSite N) : Type :=
  siteBase s ⊕ siteShift s

/-- The dimension of a site slot under the column-type
assignment `t`. -/
noncomputable def siteDim (t : LayerColumn N → charFamily G)
    (s : LayerSite N) :
    siteSlot s → ℕ
  | .inl P => charDim (t P.1)
  | .inr P => charDim (t P.1)

/-- The slot family of a site under `t`: the columns'
chosen models on the base side, their conjugate models
on the shift side. -/
noncomputable def siteFamily (t : LayerColumn N → charFamily G)
    (s : LayerSite N) :
    ∀ j : siteSlot s,
      G →* ↥(Matrix.unitaryGroup (Fin (siteDim t s j)) ℂ)
  | .inl P => charModel (t P.1)
  | .inr P => GramWordTensor.conjRep (charModel (t P.1))

/-- The channel decomposition of a site's tensor average
(A2b, applied to the site family). -/
theorem site_channel (t : LayerColumn N → charFamily G)
    (s : LayerSite N) :
    ∃ (m : ℕ) (f : Fin m → (∀ j : siteSlot s,
        Fin (siteDim t s j)) → ℂ),
      ∀ A B, tensorAvg (siteFamily t s) A B
        = ∑ i, star (f i A) * f i B := by
  classical
  exact tensorAvg_channel_form (siteFamily t s)

/-- The number of channels at a site under `t`. -/
noncomputable def siteChanCount (t : LayerColumn N → charFamily G)
    (s : LayerSite N) : ℕ :=
  Classical.choose (site_channel t s)

/-- The channel functions at a site under `t`. -/
noncomputable def siteChan (t : LayerColumn N → charFamily G)
    (s : LayerSite N) :
    Fin (siteChanCount t s)
      → (∀ j : siteSlot s, Fin (siteDim t s j)) → ℂ :=
  Classical.choose (Classical.choose_spec (site_channel t s))

/-- The site channel decomposition, chosen form. -/
theorem siteChan_spec (t : LayerColumn N → charFamily G)
    (s : LayerSite N)
    (A B : ∀ j : siteSlot s, Fin (siteDim t s j)) :
    tensorAvg (siteFamily t s) A B
      = ∑ i, star (siteChan t s i A) * siteChan t s i B :=
  Classical.choose_spec
    (Classical.choose_spec (site_channel t s)) A B

/-- The site tuple assembled from a family of column
index pairs: the outgoing component at base slots, the
incoming component at shift slots. -/
def siteTuple (t : LayerColumn N → charFamily G)
    (s : LayerSite N)
    (X : ∀ P : LayerColumn N,
      Fin (charDim (t P)) × Fin (charDim (t P))) :
    ∀ j : siteSlot s, Fin (siteDim t s j)
  | .inl P => (X P.1).1
  | .inr P => (X P.1).2

/-- The site tensor entry in column factors: the product
over base columns of the chosen models' entries, times
the product over shift columns of the conjugate
entries. -/
theorem siteTensorEntry (t : LayerColumn N → charFamily G)
    (s : LayerSite N) (g : G)
    (X Y : ∀ P : LayerColumn N,
      Fin (charDim (t P)) × Fin (charDim (t P))) :
    tensorEntry (siteFamily t s) g (siteTuple t s X)
        (siteTuple t s Y)
      = (∏ P : siteBase s,
          repMatrix (charModel (t P.1)) g ((X P.1).1) ((Y P.1).1))
        * ∏ P : siteShift s,
          star (repMatrix (charModel (t P.1)) g ((X P.1).2)
            ((Y P.1).2)) := by
  show (∏ j, repMatrix (siteFamily t s j) g (siteTuple t s X j)
      (siteTuple t s Y j)) = _
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact Finset.prod_congr rfl fun P _ => rfl
  · refine Finset.prod_congr rfl fun P _ => ?_
    show repMatrix (GramWordTensor.conjRep (charModel (t P.1))) g
        ((X P.1).2) ((Y P.1).2)
      = star (repMatrix (charModel (t P.1)) g ((X P.1).2)
          ((Y P.1).2))
    rw [GramWordTensor.repMatrix_conjRep,
      GramWordTensor.conjMat_apply]

/-- **Site regrouping of the α-letters.**  The product
over columns of (base entry at the column's base site)
× (conjugate shift entry at its shift-target) is the
product over sites of the site tensor entries. -/
theorem prod_site_regroup (t : LayerColumn N → charFamily G)
    (α : LayerSite N → G)
    (X Y : ∀ P : LayerColumn N,
      Fin (charDim (t P)) × Fin (charDim (t P))) :
    (∏ P : LayerColumn N,
        repMatrix (charModel (t P)) (α P.1) ((X P).1) ((Y P).1)
        * star (repMatrix (charModel (t P))
            (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2) ((Y P).2)))
      = ∏ s : LayerSite N, tensorEntry (siteFamily t s) (α s)
          (siteTuple t s X) (siteTuple t s Y) := by
  classical
  have hF : (∏ P : LayerColumn N,
        repMatrix (charModel (t P)) (α P.1) ((X P).1) ((Y P).1))
      = ∏ s : LayerSite N, ∏ P : siteBase s,
          repMatrix (charModel (t P.1)) (α s) ((X P.1).1)
            ((Y P.1).1) := by
    rw [← Finset.prod_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (LayerColumn N)))
      (t := (Finset.univ : Finset (LayerSite N)))
      (g := fun P : LayerColumn N => P.1)
      (fun P _ => Finset.mem_univ P.1)]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.prod_subtype
      (Finset.univ.filter (fun P : LayerColumn N => P.1 = s))
      (fun _ => Iff.rfl)]
    exact Finset.prod_congr rfl fun P _ => by
      rw [(Finset.mem_filter.mp P.2).2]
  have hG : (∏ P : LayerColumn N,
        star (repMatrix (charModel (t P))
          (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2) ((Y P).2)))
      = ∏ s : LayerSite N, ∏ P : siteShift s,
          star (repMatrix (charModel (t P.1)) (α s) ((X P.1).2)
            ((Y P.1).2)) := by
    rw [← Finset.prod_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (LayerColumn N)))
      (t := (Finset.univ : Finset (LayerSite N)))
      (g := fun P : LayerColumn N =>
        layerShift P.2.1 P.2.2 P.1)
      (fun P _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.prod_subtype
      (Finset.univ.filter (fun P : LayerColumn N =>
        layerShift P.2.1 P.2.2 P.1 = s))
      (fun _ => Iff.rfl)]
    exact Finset.prod_congr rfl fun P _ => by
      rw [(Finset.mem_filter.mp P.2).2]
  rw [Finset.prod_mul_distrib, hF, hG, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [siteTensorEntry]

/-- **Factorization of the stratum sum.**  The counting
average over site configurations of a product of
site-local factors is the product of the counting
averages. -/
theorem sum_alpha_factor (F : LayerSite N → G → ℂ) :
    ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G, ∏ s, F s (α s)
      = ∏ s, ((Fintype.card G : ℂ))⁻¹ * ∑ g, F s g := by
  have hsum : (∑ α : LayerSite N → G, ∏ s, F s (α s))
      = ∏ s, ∑ g, F s g := by
    have h := Finset.sum_prod_piFinset
      (Finset.univ : Finset G) (fun s g => F s g)
    rwa [Fintype.piFinset_univ] at h
  rw [hsum, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun]
  push_cast
  rw [inv_pow]

/-- **The separated feature** of a column-type assignment
`t` and a channel tuple `c`: the sum over column index
pairs of the channels' outgoing factors times the
product of the `u`-letters' inverse entries. -/
noncomputable def charSepFeat (t : LayerColumn N → charFamily G)
    (c : ∀ s : LayerSite N, Fin (siteChanCount t s))
    (v : LayerLink N → G) : ℂ :=
  ∑ X : ∀ P : LayerColumn N,
      Fin (charDim (t P)) × Fin (charDim (t P)),
    (∏ s, star (siteChan t s (c s) (siteTuple t s X)))
      * ∏ P, repMatrix (charModel (t P)) ((v (colLink P))⁻¹)
          ((X P).2) ((X P).1)

/-- **The separation identity (B2 core).**  For every
column-type assignment `t`, the counting average over
stratum configurations of the product of the columns'
characters at their column words separates over the
channel tuples: it is the sum over `c` of
`feat c u * star (feat c u')`. -/
theorem char_separation (t : LayerColumn N → charFamily G)
    (u u' : LayerLink N → G) :
    ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G,
          ∏ P : LayerColumn N, (t P).1 (colWordOf u u' P α)
      = ∑ c : ∀ s : LayerSite N, Fin (siteChanCount t s),
        charSepFeat t c u * star (charSepFeat t c u') := by
  classical
  -- per-column word expansion
  have hexp : ∀ (α : LayerSite N → G) (P : LayerColumn N),
      (t P).1 (colWordOf u u' P α)
        = ∑ X : Fin (charDim (t P)) × Fin (charDim (t P)),
          ∑ Y : Fin (charDim (t P)) × Fin (charDim (t P)),
          repMatrix (charModel (t P)) (α P.1) X.1 Y.1
            * repMatrix (charModel (t P)) (u' (colLink P)) Y.1 Y.2
            * star (repMatrix (charModel (t P))
                (α (layerShift P.2.1 P.2.2 P.1)) X.2 Y.2)
            * repMatrix (charModel (t P)) ((u (colLink P))⁻¹)
                X.2 X.1 := by
    intro α P
    have h2 : colWordOf u u' P α
        = α P.1 * u' (colLink P)
          * (α (layerShift P.2.1 P.2.2 P.1))⁻¹
          * (u (colLink P))⁻¹ := rfl
    rw [← charModel_charFn (t P), h2]
    exact charFn_word_expand _ _ _ _ _
  -- the feature, unfolded
  have hfeat : ∀ (c : ∀ s : LayerSite N, Fin (siteChanCount t s))
      (v : LayerLink N → G),
      charSepFeat t c v
        = ∑ X : ∀ P : LayerColumn N,
            Fin (charDim (t P)) × Fin (charDim (t P)),
          (∏ s, star (siteChan t s (c s) (siteTuple t s X)))
            * ∏ P, repMatrix (charModel (t P)) ((v (colLink P))⁻¹)
                ((X P).2) ((X P).1) :=
    fun c v => rfl
  -- the star of a feature is the incoming factor
  have hstar : ∀ (c : ∀ s : LayerSite N, Fin (siteChanCount t s))
      (v : LayerLink N → G),
      star (charSepFeat t c v)
        = ∑ Y : ∀ P : LayerColumn N,
            Fin (charDim (t P)) × Fin (charDim (t P)),
          (∏ s, siteChan t s (c s) (siteTuple t s Y))
            * ∏ P, repMatrix (charModel (t P)) (v (colLink P))
                ((Y P).1) ((Y P).2) := by
    intro c v
    rw [hfeat, star_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [star_mul, star_prod, star_star]
    conv_lhs => rw [mul_comm]
    refine congrArg₂ (· * ·) rfl ?_
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [GramWordTensor.repMatrix_inv_entry,
      GramWordTensor.repMatrix_conjRep,
      GramWordTensor.conjMat_apply, star_star]
  -- regrouping of the four letter factors
  have hreg : ∀ (α : LayerSite N → G)
      (X Y : ∀ P : LayerColumn N,
        Fin (charDim (t P)) × Fin (charDim (t P))),
      (∏ P, repMatrix (charModel (t P)) (α P.1) ((X P).1) ((Y P).1)
        * repMatrix (charModel (t P)) (u' (colLink P))
            ((Y P).1) ((Y P).2)
        * star (repMatrix (charModel (t P))
            (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2) ((Y P).2))
        * repMatrix (charModel (t P)) ((u (colLink P))⁻¹)
            ((X P).2) ((X P).1))
      = (∏ P, repMatrix (charModel (t P)) (u' (colLink P))
            ((Y P).1) ((Y P).2))
        * (∏ P, repMatrix (charModel (t P)) ((u (colLink P))⁻¹)
            ((X P).2) ((X P).1))
        * ∏ P, (repMatrix (charModel (t P)) (α P.1)
            ((X P).1) ((Y P).1)
          * star (repMatrix (charModel (t P))
              (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2)
                ((Y P).2))) := by
    intro α X Y
    simp only [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    ring
  -- step A: expansion + regrouping under the α-sum
  have stepA : ∀ α : LayerSite N → G,
      ∏ P : LayerColumn N, (t P).1 (colWordOf u u' P α)
        = ∑ X : ∀ P : LayerColumn N,
            Fin (charDim (t P)) × Fin (charDim (t P)),
          ∑ Y : ∀ P : LayerColumn N,
            Fin (charDim (t P)) × Fin (charDim (t P)),
          (∏ P, repMatrix (charModel (t P)) (u' (colLink P))
              ((Y P).1) ((Y P).2))
          * (∏ P, repMatrix (charModel (t P)) ((u (colLink P))⁻¹)
              ((X P).2) ((X P).1))
          * ∏ P, (repMatrix (charModel (t P)) (α P.1)
              ((X P).1) ((Y P).1)
            * star (repMatrix (charModel (t P))
                (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2)
                  ((Y P).2))) := by
    intro α
    rw [Finset.prod_congr rfl (fun P _ => hexp α P)]
    simp only [Fintype.prod_sum]
    exact Finset.sum_congr rfl fun X _ =>
      Finset.sum_congr rfl fun Y _ => hreg α X Y
  -- step B: the α-average of the regrouped letters is the
  -- product of site tensor averages
  have stepB : ∀ (X Y : ∀ P : LayerColumn N,
        Fin (charDim (t P)) × Fin (charDim (t P))),
      ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G,
          ∏ P, (repMatrix (charModel (t P)) (α P.1)
              ((X P).1) ((Y P).1)
            * star (repMatrix (charModel (t P))
                (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2)
                  ((Y P).2)))
      = ∏ s, tensorAvg (siteFamily t s) (siteTuple t s X)
          (siteTuple t s Y) := by
    intro X Y
    have h := sum_alpha_factor
      (fun s g => tensorEntry (siteFamily t s) g
        (siteTuple t s X) (siteTuple t s Y))
    show ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G,
          ∏ P, (repMatrix (charModel (t P)) (α P.1)
              ((X P).1) ((Y P).1)
            * star (repMatrix (charModel (t P))
                (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2)
                  ((Y P).2)))
      = ∏ s, ((Fintype.card G : ℂ))⁻¹
          * ∑ g, tensorEntry (siteFamily t s) g
              (siteTuple t s X) (siteTuple t s Y)
    rw [← h]
    refine congrArg _ (Finset.sum_congr rfl fun α _ => ?_)
    exact prod_site_regroup t α X Y
  -- step C: assemble — swap the α-sum inside, apply step B,
  -- split the site averages into channels, and factor the
  -- (X, Y) sum into the two features
  calc ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
        * ∑ α : LayerSite N → G,
          ∏ P : LayerColumn N, (t P).1 (colWordOf u u' P α)
      = ∑ X : ∀ P : LayerColumn N,
          Fin (charDim (t P)) × Fin (charDim (t P)),
        ∑ Y : ∀ P : LayerColumn N,
          Fin (charDim (t P)) × Fin (charDim (t P)),
        (∏ P, repMatrix (charModel (t P)) (u' (colLink P))
            ((Y P).1) ((Y P).2))
        * (∏ P, repMatrix (charModel (t P)) ((u (colLink P))⁻¹)
            ((X P).2) ((X P).1))
        * (∏ s, tensorAvg (siteFamily t s) (siteTuple t s X)
            (siteTuple t s Y)) := by
        rw [Finset.sum_congr rfl (fun α _ => stepA α)]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun X _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [Finset.sum_congr rfl (fun α _ => show
          ((Fintype.card (LayerSite N → G) : ℂ))⁻¹
            * ((∏ P, repMatrix (charModel (t P)) (u' (colLink P))
                  ((Y P).1) ((Y P).2))
              * (∏ P, repMatrix (charModel (t P))
                  ((u (colLink P))⁻¹) ((X P).2) ((X P).1))
              * ∏ P, (repMatrix (charModel (t P)) (α P.1)
                  ((X P).1) ((Y P).1)
                * star (repMatrix (charModel (t P))
                    (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2)
                      ((Y P).2))))
          = (∏ P, repMatrix (charModel (t P)) (u' (colLink P))
                ((Y P).1) ((Y P).2))
            * (∏ P, repMatrix (charModel (t P))
                ((u (colLink P))⁻¹) ((X P).2) ((X P).1))
            * (((Fintype.card (LayerSite N → G) : ℂ))⁻¹
              * ∏ P, (repMatrix (charModel (t P)) (α P.1)
                  ((X P).1) ((Y P).1)
                * star (repMatrix (charModel (t P))
                    (α (layerShift P.2.1 P.2.2 P.1)) ((X P).2)
                      ((Y P).2)))) from by ring),
          ← Finset.mul_sum, ← Finset.mul_sum, stepB X Y]
    _ = ∑ X : ∀ P : LayerColumn N,
          Fin (charDim (t P)) × Fin (charDim (t P)),
        ∑ Y : ∀ P : LayerColumn N,
          Fin (charDim (t P)) × Fin (charDim (t P)),
        (∏ P, repMatrix (charModel (t P)) (u' (colLink P))
            ((Y P).1) ((Y P).2))
        * (∏ P, repMatrix (charModel (t P)) ((u (colLink P))⁻¹)
            ((X P).2) ((X P).1))
        * ∑ c : ∀ s : LayerSite N, Fin (siteChanCount t s),
          ∏ s, (star (siteChan t s (c s) (siteTuple t s X))
            * siteChan t s (c s) (siteTuple t s Y)) := by
        refine Finset.sum_congr rfl fun X _ =>
          Finset.sum_congr rfl fun Y _ => ?_
        refine congrArg₂ (· * ·) rfl ?_
        rw [Finset.prod_congr rfl
          (fun s _ => siteChan_spec t s _ _)]
        exact Fintype.prod_sum _
    _ = ∑ c : ∀ s : LayerSite N, Fin (siteChanCount t s),
        charSepFeat t c u * star (charSepFeat t c u') := by
        have hswap : ∀ (F : (∀ P : LayerColumn N,
              Fin (charDim (t P)) × Fin (charDim (t P)))
            → (∀ P : LayerColumn N,
              Fin (charDim (t P)) × Fin (charDim (t P)))
            → (∀ s : LayerSite N, Fin (siteChanCount t s)) → ℂ),
            (∑ X, ∑ Y, ∑ c, F X Y c)
              = ∑ c, ∑ X, ∑ Y, F X Y c :=
          fun F => (Finset.sum_congr rfl fun X _ =>
            Finset.sum_comm).trans Finset.sum_comm
        simp only [Finset.mul_sum]
        rw [hswap]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hterm : ∀ (X Y : ∀ P : LayerColumn N,
            Fin (charDim (t P)) × Fin (charDim (t P))),
            ((∏ P, repMatrix (charModel (t P)) (u' (colLink P))
                ((Y P).1) ((Y P).2))
              * (∏ P, repMatrix (charModel (t P))
                  ((u (colLink P))⁻¹) ((X P).2) ((X P).1)))
              * ∏ s, (star (siteChan t s (c s) (siteTuple t s X))
                * siteChan t s (c s) (siteTuple t s Y))
            = ((∏ s, star (siteChan t s (c s) (siteTuple t s X)))
                * ∏ P, repMatrix (charModel (t P))
                    ((u (colLink P))⁻¹) ((X P).2) ((X P).1))
              * ((∏ s, siteChan t s (c s) (siteTuple t s Y))
                * ∏ P, repMatrix (charModel (t P))
                    (u' (colLink P)) ((Y P).1) ((Y P).2)) := by
          intro X Y
          rw [Finset.prod_mul_distrib]
          ring
        rw [Finset.sum_congr rfl (fun X _ =>
          Finset.sum_congr rfl fun Y _ => hterm X Y),
          hfeat, hstar c u', ← Finset.sum_mul_sum]

end CharSeparation

end ThetLogos
