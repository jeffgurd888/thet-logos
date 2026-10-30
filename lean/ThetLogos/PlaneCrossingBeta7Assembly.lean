/-
# ThetLogos.PlaneCrossingBeta7Assembly — B7-2a: the order-7
assembly opens: the `Θ(1,3,3)` book-support family, the
family channel sums on the 6- and 7-supports, and the
seven channel excesses

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
0/4. This is an OPENING brick (B7-2a) for the order-7
assembly, at general `(G, ρ)` — no irreducibility
anywhere: it owns the support family for B7-0's card-7
pattern (`HasSevenPatternTheta133`, the book support:
two unit plaquettes sharing one column), the channel
sums over the support families that B7-1b deferred
(the `(2,1,1,1,1,1)` channels on the `C₆` and
`Θ(2,2,2)` families — constructed at B6-2a and reused
here — and the `(1⁷)` channel on the book family), and
the seven channel excesses with their baseline
bookkeeping. Definitions and baseline bookkeeping only.
**No assembly identity is asserted here** (that is
B7-2b, over the order-7 total decomposition), and **no
sign is asserted for any channel or excess**: the β⁷
general sign is FRONTIER — its new channels carry
still higher entry multiplicities at a site than the
order-6 channels, on top of the still-unowned (2,1)
triple twirl that already blocks the β⁵ general sign.

**Baselines.** Each excess removes, summand by summand,
the fully-split value of its moment's factor pattern —
the `e₁`-monomial shapes the fibers force:
`(4,1,1,1) ↦ μ₄e₁³`, `(3,2,1,1) ↦ μ₃μ₂e₁²`,
`(2,2,2,1) ↦ μ₂³e₁`, `(2,1,1,1,1,1) ↦ μ₂e₁⁵`, and the
all-ones book pattern `(1⁷) ↦ e₁⁷`. These are the
assembly's candidate baselines, validated or corrected
at B7-2b.

**The ADJ/OPP bookkeeping.** For the `(3,2,1,1)`
channel, B7-1b split the raw sum by the heavy pair's
relative position (ADJACENT / OPPOSITE). Unlike the
other channels, the number of heavy pairs of each type
over a primitive quad is not a universal constant of
the quad family asserted anywhere in the tree, so the
baseline totals of the two split excesses are carried
here as explicit counting sums (`kappa7adjPairCount`,
`kappa7oppPairCount`), not as numerals. What *is*
proved numerically is the combined statement: the two
split excesses sum to the unsplit `(3,2,1,1)` excess,
whose baseline total is the constant `12` per quad
(four tripled choices × three doubled choices). No
numeral is claimed for either side separately.

**Support families.** The `C₆` / `Θ(2,2,2)` families
(`c6Supports`, `thetaSupports`) are consumed from
B6-2a, not reconstructed. The book family is
constructed here, in exactly the form of
`primitiveQuads` in `PlaneCrossingBeta4`: a filter of
the universal finset by a card condition together with
the pattern predicate exported by B7-0
(`OrderSevenSelection`). The predicate is consumed as
exported, not restated.
-/

import Mathlib.Data.Nat.Choose.Multinomial
import ThetLogos.PlaneCrossingBeta7
import ThetLogos.PlaneCrossingBeta6Assembly

open MeasureTheory Finset

namespace ThetLogos

section Supports7

variable {N : ℕ} [NeZero N]

open Classical in
/-- The finite set of 7-element supports carrying the
`Θ(1,3,3)` book pattern of B7-0
(`HasSevenPatternTheta133`), constructed as
`primitiveQuads` is constructed: a filter of the
universal finset by card and pattern. -/
noncomputable def theta133Supports :
    Finset (Finset (LayerColumn N)) :=
  Finset.univ.filter (fun S => S.card = 7
    ∧ HasSevenPatternTheta133 S)

/-- A book support has seven columns. -/
theorem card_eq_seven_of_mem_theta133Supports
    {S : Finset (LayerColumn N)}
    (hS : S ∈ theta133Supports) : S.card = 7 := by
  classical
  rw [theta133Supports, Finset.mem_filter] at hS
  exact hS.2.1

/-- A book support carries the `Θ(1,3,3)` pattern. -/
theorem hasSevenPatternTheta133_of_mem_theta133Supports
    {S : Finset (LayerColumn N)}
    (hS : S ∈ theta133Supports) :
    HasSevenPatternTheta133 S := by
  classical
  rw [theta133Supports, Finset.mem_filter] at hS
  exact hS.2.2

end Supports7

section Assembly7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-! ## Family channel sums (B7-1b's deferred sums) -/

/-- **The `(2,1,1,1,1,1)` channel on `C₆` supports**:
the sum, over the card-6 `C₆` supports (the family
constructed at B6-2a), of B7-1b's raw per-support
channel `kappa7chan211111C6`. Raw channel expression
only: no assembly identity and no sign is asserted
for this sum. -/
noncomputable def kappa7chan211111C6Sum
    (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ c6Supports, kappa7chan211111C6 ρ μG S u u'

/-- **The `(2,1,1,1,1,1)` channel on `Θ(2,2,2)`
supports**: the sum, over the card-6 `Θ` supports, of
B7-1b's raw per-support channel
`kappa7chan211111Theta`. Raw channel expression only,
on the same fence as `kappa7chan211111C6Sum`. -/
noncomputable def kappa7chan211111ThetaSum
    (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ thetaSupports, kappa7chan211111Theta ρ μG S u u'

/-- **The `(1⁷)` channel on the `Θ(1,3,3)` book
supports**: the sum, over the card-7 book supports, of
B7-1b's raw per-support channel `kappa7chanTheta133`
(the multiplicity-free moment `heptaReMoment`). Raw
channel expression only, on the same fence as
`kappa7chan211111C6Sum`. -/
noncomputable def kappa7chanTheta133Sum
    (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ theta133Supports, kappa7chanTheta133 ρ μG S u u'

/-! ## The primitive-quad channel excesses -/

/-- **The `(4,1,1,1)` channel excess**: the channel sum
of B7-1b with its fully-split baseline `μ₄e₁³` removed
summand by summand. No sign is asserted for it. -/
noncomputable def kappa7chan4111Excess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    (quadrupledQuadReMoment ρ μG C P u u'
      - realMoment ρ μG 4 * (e1 ρ μG) ^ 3)

/-- The `(4,1,1,1)` channel excess is the raw channel
sum minus its baseline: each primitive quad contributes
four quadrupled columns, each carrying baseline
`μ₄e₁³`. -/
theorem kappa7chan4111Excess_eq (u u' : LayerLink N → G) :
    kappa7chan4111Excess ρ μG u u'
      = kappa7chan4111 ρ μG u u'
        - 4 * ((primitiveQuads (N := N)).card : ℝ)
          * realMoment ρ μG 4 * (e1 ρ μG) ^ 3 := by
  classical
  have hbase : ∀ C ∈ primitiveQuads (N := N),
      ∑ _P ∈ C, (realMoment ρ μG 4 * (e1 ρ μG) ^ 3)
        = 4 * (realMoment ρ μG 4 * (e1 ρ μG) ^ 3) := by
    intro C hC
    have hC4 : C.card = 4 := (Finset.mem_filter.mp hC).2.1
    rw [Finset.sum_const, hC4, nsmul_eq_mul, Nat.cast_ofNat]
  have step1 : kappa7chan4111Excess ρ μG u u'
      = kappa7chan4111 ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ _P ∈ C,
            (realMoment ρ μG 4 * (e1 ρ μG) ^ 3) := by
    unfold kappa7chan4111Excess kappa7chan4111
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ _P ∈ C,
        (realMoment ρ μG 4 * (e1 ρ μG) ^ 3))
      = 4 * ((primitiveQuads (N := N)).card : ℝ)
        * realMoment ρ μG 4 * (e1 ρ μG) ^ 3 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-- **The `(2,2,2,1)` channel excess**: the channel sum
of B7-1b with its fully-split baseline `μ₂³e₁` removed
summand by summand. No sign is asserted for it. -/
noncomputable def kappa7chan2221Excess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    ∑ R ∈ (C.erase P).erase Q,
      (doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
        - (realMoment ρ μG 2) ^ 3 * e1 ρ μG)

/-- The `(2,2,2,1)` channel excess is the raw channel
sum minus its baseline: each primitive quad contributes
twenty-four ordered triples of pairwise distinct doubled
columns (`4 · 3 · 2`), each carrying baseline `μ₂³e₁`. -/
theorem kappa7chan2221Excess_eq (u u' : LayerLink N → G) :
    kappa7chan2221Excess ρ μG u u'
      = kappa7chan2221 ρ μG u u'
        - 24 * ((primitiveQuads (N := N)).card : ℝ)
          * (realMoment ρ μG 2) ^ 3 * e1 ρ μG := by
  classical
  have hbase : ∀ C ∈ primitiveQuads (N := N),
      ∑ P ∈ C, ∑ Q ∈ C.erase P, ∑ _R ∈ (C.erase P).erase Q,
          ((realMoment ρ μG 2) ^ 3 * e1 ρ μG)
        = 24 * ((realMoment ρ μG 2) ^ 3 * e1 ρ μG) := by
    intro C hC
    have hC4 : C.card = 4 := (Finset.mem_filter.mp hC).2.1
    have hR : ∀ P ∈ C, ∀ Q ∈ C.erase P,
        ∑ _R ∈ (C.erase P).erase Q,
            ((realMoment ρ μG 2) ^ 3 * e1 ρ μG)
          = 2 * ((realMoment ρ μG 2) ^ 3 * e1 ρ μG) := by
      intro P hP Q hQ
      have hQcard : (C.erase P).card = 3 := by
        rw [Finset.card_erase_of_mem hP, hC4]
      rw [Finset.sum_const,
        Finset.card_erase_of_mem hQ, hQcard, nsmul_eq_mul]
      norm_num
    have hQ : ∀ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ _R ∈ (C.erase P).erase Q,
            ((realMoment ρ μG 2) ^ 3 * e1 ρ μG)
          = 6 * ((realMoment ρ μG 2) ^ 3 * e1 ρ μG) := by
      intro P hP
      rw [Finset.sum_congr rfl (hR P hP), Finset.sum_const,
        Finset.card_erase_of_mem hP, hC4, nsmul_eq_mul]
      norm_num
      ring
    rw [Finset.sum_congr rfl hQ, Finset.sum_const, hC4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have step1 : kappa7chan2221Excess ρ μG u u'
      = kappa7chan2221 ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
            ∑ Q ∈ C.erase P, ∑ _R ∈ (C.erase P).erase Q,
              ((realMoment ρ μG 2) ^ 3 * e1 ρ μG) := by
    unfold kappa7chan2221Excess kappa7chan2221
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun Q _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
        ∑ Q ∈ C.erase P, ∑ _R ∈ (C.erase P).erase Q,
          ((realMoment ρ μG 2) ^ 3 * e1 ρ μG))
      = 24 * ((primitiveQuads (N := N)).card : ℝ)
        * (realMoment ρ μG 2) ^ 3 * e1 ρ μG := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-! ## The `(3,2,1,1)` channel excesses (combined and split) -/

/-- **The `(3,2,1,1)` channel excess (unsplit)**: the
channel sum of B7-1b with its fully-split baseline
`μ₃μ₂e₁²` removed summand by summand. No sign is
asserted for it. -/
noncomputable def kappa7chan3211Excess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    (tripledDoubledQuadReMoment ρ μG C P Q u u'
      - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)

/-- The unsplit `(3,2,1,1)` channel excess is the raw
channel sum minus its baseline: each primitive quad
contributes twelve ordered heavy pairs (`4 · 3`), each
carrying baseline `μ₃μ₂e₁²`. -/
theorem kappa7chan3211Excess_eq (u u' : LayerLink N → G) :
    kappa7chan3211Excess ρ μG u u'
      = kappa7chan3211 ρ μG u u'
        - 12 * ((primitiveQuads (N := N)).card : ℝ)
          * realMoment ρ μG 3 * realMoment ρ μG 2
          * (e1 ρ μG) ^ 2 := by
  classical
  have hbase : ∀ C ∈ primitiveQuads (N := N),
      ∑ P ∈ C, ∑ _Q ∈ C.erase P,
          (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)
        = 12 * (realMoment ρ μG 3 * realMoment ρ μG 2
            * (e1 ρ μG) ^ 2) := by
    intro C hC
    have hC4 : C.card = 4 := (Finset.mem_filter.mp hC).2.1
    have hinner : ∀ P ∈ C,
        ∑ _Q ∈ C.erase P,
            (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)
          = 3 * (realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2) := by
      intro P hP
      rw [Finset.sum_const, Finset.card_erase_of_mem hP, hC4,
        nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, hC4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have step1 : kappa7chan3211Excess ρ μG u u'
      = kappa7chan3211 ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C, ∑ _Q ∈ C.erase P,
            (realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2) := by
    unfold kappa7chan3211Excess kappa7chan3211
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
        ∑ _Q ∈ C.erase P,
          (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2))
      = 12 * ((primitiveQuads (N := N)).card : ℝ)
        * realMoment ρ μG 3 * realMoment ρ μG 2
        * (e1 ρ μG) ^ 2 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-- The number of ADJACENT ordered heavy pairs, summed
over all primitive quads and tripled columns: the
baseline multiplicity of the ADJACENT `(3,2,1,1)`
excess. Carried as an explicit counting sum — no
numeral is asserted for it (see the header). -/
noncomputable def kappa7adjPairCount : ℝ :=
  ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
    (((C.erase P).filter (fun Q => ColsShareSite P Q)).card : ℝ)

/-- The number of OPPOSITE ordered heavy pairs, summed
over all primitive quads and tripled columns: the
baseline multiplicity of the OPPOSITE `(3,2,1,1)`
excess. The twin of `kappa7adjPairCount`. -/
noncomputable def kappa7oppPairCount : ℝ :=
  ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
    (((C.erase P).filter
      (fun Q => ColsDisjointSites P Q)).card : ℝ)

/-- **The ADJACENT `(3,2,1,1)` channel excess**: the
ADJACENT channel sum of B7-1b with its fully-split
baseline `μ₃μ₂e₁²` removed summand by summand. No sign
is asserted for it. -/
noncomputable def kappa7chan3211AdjExcess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    ∑ Q ∈ (C.erase P).filter (fun Q => ColsShareSite P Q),
      (tripledDoubledQuadReMoment ρ μG C P Q u u'
        - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)

/-- **The OPPOSITE `(3,2,1,1)` channel excess**: the
OPPOSITE channel sum of B7-1b with its fully-split
baseline `μ₃μ₂e₁²` removed summand by summand. No sign
is asserted for it. -/
noncomputable def kappa7chan3211OppExcess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    ∑ Q ∈ (C.erase P).filter (fun Q => ColsDisjointSites P Q),
      (tripledDoubledQuadReMoment ρ μG C P Q u u'
        - realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)

/-- The ADJACENT `(3,2,1,1)` channel excess is the raw
ADJACENT channel sum minus its baseline total: the
baseline `μ₃μ₂e₁²` carried once per adjacent heavy
pair, counted by `kappa7adjPairCount`. -/
theorem kappa7chan3211AdjExcess_eq (u u' : LayerLink N → G) :
    kappa7chan3211AdjExcess ρ μG u u'
      = kappa7chan3211Adj ρ μG u u'
        - kappa7adjPairCount (N := N)
          * realMoment ρ μG 3 * realMoment ρ μG 2
          * (e1 ρ μG) ^ 2 := by
  classical
  have step1 : kappa7chan3211AdjExcess ρ μG u u'
      = kappa7chan3211Adj ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
            ∑ _Q ∈ (C.erase P).filter (fun Q => ColsShareSite P Q),
              (realMoment ρ μG 3 * realMoment ρ μG 2
                * (e1 ρ μG) ^ 2) := by
    unfold kappa7chan3211AdjExcess kappa7chan3211Adj
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
        ∑ _Q ∈ (C.erase P).filter (fun Q => ColsShareSite P Q),
          (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2))
      = kappa7adjPairCount (N := N)
        * realMoment ρ μG 3 * realMoment ρ μG 2
        * (e1 ρ μG) ^ 2 := by
    have hinner : ∀ C ∈ primitiveQuads (N := N), ∀ P ∈ C,
        ∑ _Q ∈ (C.erase P).filter (fun Q => ColsShareSite P Q),
            (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)
          = (((C.erase P).filter
              (fun Q => ColsShareSite P Q)).card : ℝ)
            * (realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2) := by
      intro C _ P _
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun C hC =>
      Finset.sum_congr rfl (hinner C hC)]
    have hRHS : kappa7adjPairCount (N := N)
        * realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2
        = (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
            (((C.erase P).filter
              (fun Q => ColsShareSite P Q)).card : ℝ))
          * (realMoment ρ μG 3 * realMoment ρ μG 2
            * (e1 ρ μG) ^ 2) := by
      unfold kappa7adjPairCount
      ring
    rw [hRHS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_mul]
  rw [step1, step2]

/-- The OPPOSITE `(3,2,1,1)` channel excess is the raw
OPPOSITE channel sum minus its baseline total: the
baseline `μ₃μ₂e₁²` carried once per opposite heavy
pair, counted by `kappa7oppPairCount`. -/
theorem kappa7chan3211OppExcess_eq (u u' : LayerLink N → G) :
    kappa7chan3211OppExcess ρ μG u u'
      = kappa7chan3211Opp ρ μG u u'
        - kappa7oppPairCount (N := N)
          * realMoment ρ μG 3 * realMoment ρ μG 2
          * (e1 ρ μG) ^ 2 := by
  classical
  have step1 : kappa7chan3211OppExcess ρ μG u u'
      = kappa7chan3211Opp ρ μG u u'
        - ∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
            ∑ _Q ∈ (C.erase P).filter
                (fun Q => ColsDisjointSites P Q),
              (realMoment ρ μG 3 * realMoment ρ μG 2
                * (e1 ρ μG) ^ 2) := by
    unfold kappa7chan3211OppExcess kappa7chan3211Opp
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
        ∑ _Q ∈ (C.erase P).filter
            (fun Q => ColsDisjointSites P Q),
          (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2))
      = kappa7oppPairCount (N := N)
        * realMoment ρ μG 3 * realMoment ρ μG 2
        * (e1 ρ μG) ^ 2 := by
    have hinner : ∀ C ∈ primitiveQuads (N := N), ∀ P ∈ C,
        ∑ _Q ∈ (C.erase P).filter
            (fun Q => ColsDisjointSites P Q),
            (realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2)
          = (((C.erase P).filter
              (fun Q => ColsDisjointSites P Q)).card : ℝ)
            * (realMoment ρ μG 3 * realMoment ρ μG 2
              * (e1 ρ μG) ^ 2) := by
      intro C _ P _
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun C hC =>
      Finset.sum_congr rfl (hinner C hC)]
    have hRHS : kappa7oppPairCount (N := N)
        * realMoment ρ μG 3 * realMoment ρ μG 2 * (e1 ρ μG) ^ 2
        = (∑ C ∈ primitiveQuads (N := N), ∑ P ∈ C,
            (((C.erase P).filter
              (fun Q => ColsDisjointSites P Q)).card : ℝ))
          * (realMoment ρ μG 3 * realMoment ρ μG 2
            * (e1 ρ μG) ^ 2) := by
      unfold kappa7oppPairCount
      ring
    rw [hRHS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_mul]
  rw [step1, step2]

/-- **The split excesses sum to the unsplit excess.**
The ADJACENT and OPPOSITE `(3,2,1,1)` excesses sum to
the unsplit `(3,2,1,1)` excess: at every heavy pair
the dichotomy of B7-0 is exhaustive and the two sides
are complementary, so the complementary-filter sum
identity applies summand by summand — the same
partition as `kappa7chan3211_adj_add_opp`, carried
through the baseline subtraction. -/
theorem kappa7chan3211Adj_add_Opp_excess
    (u u' : LayerLink N → G) :
    kappa7chan3211AdjExcess ρ μG u u'
      + kappa7chan3211OppExcess ρ μG u u'
      = kappa7chan3211Excess ρ μG u u' := by
  classical
  unfold kappa7chan3211AdjExcess kappa7chan3211OppExcess
    kappa7chan3211Excess
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hnot : (C.erase P).filter (fun Q => ColsDisjointSites P Q)
      = (C.erase P).filter (fun Q => ¬ ColsShareSite P Q) :=
    Finset.filter_congr fun Q _ =>
      colsDisjointSites_iff_not_share P Q
  rw [hnot, Finset.sum_filter_add_sum_filter_not]

/-! ## The 6-support and book-support channel excesses -/

/-- **The `(2,1,1,1,1,1)` channel excess on `C₆`
supports**: the `C₆` family channel sum with its
fully-split baseline `μ₂e₁⁵` removed summand by
summand (per support, per doubled column). No sign is
asserted for it. -/
noncomputable def kappa7chan211111C6Excess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ c6Supports, ∑ P ∈ S,
    (doubledHexaReMoment ρ μG S P u u'
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)

/-- The `C₆` `(2,1,1,1,1,1)` channel excess is the raw
family channel sum minus its baseline: each `C₆`
support contributes six doubled columns, each carrying
baseline `μ₂e₁⁵`. -/
theorem kappa7chan211111C6Excess_eq (u u' : LayerLink N → G) :
    kappa7chan211111C6Excess ρ μG u u'
      = kappa7chan211111C6Sum ρ μG u u'
        - 6 * ((c6Supports (N := N)).card : ℝ)
          * realMoment ρ μG 2 * (e1 ρ μG) ^ 5 := by
  classical
  have hbase : ∀ S ∈ c6Supports (N := N),
      ∑ _P ∈ S, (realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
        = 6 * (realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
    intro S hS
    have hS6 : S.card = 6 := card_eq_six_of_mem_c6Supports hS
    rw [Finset.sum_const, hS6, nsmul_eq_mul, Nat.cast_ofNat]
  have step1 : kappa7chan211111C6Excess ρ μG u u'
      = kappa7chan211111C6Sum ρ μG u u'
        - ∑ S ∈ c6Supports (N := N), ∑ _P ∈ S,
            (realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
    unfold kappa7chan211111C6Excess kappa7chan211111C6Sum
      kappa7chan211111C6
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ S ∈ c6Supports (N := N), ∑ _P ∈ S,
        (realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = 6 * ((c6Supports (N := N)).card : ℝ)
        * realMoment ρ μG 2 * (e1 ρ μG) ^ 5 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-- **The `(2,1,1,1,1,1)` channel excess on `Θ(2,2,2)`
supports**: the `Θ` family channel sum with its
fully-split baseline `μ₂e₁⁵` removed summand by
summand (per support, per doubled column). No sign is
asserted for it. -/
noncomputable def kappa7chan211111ThetaExcess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ thetaSupports, ∑ P ∈ S,
    (doubledHexaReMoment ρ μG S P u u'
      - realMoment ρ μG 2 * (e1 ρ μG) ^ 5)

/-- The `Θ` `(2,1,1,1,1,1)` channel excess is the raw
family channel sum minus its baseline: each `Θ`
support contributes six doubled columns, each carrying
baseline `μ₂e₁⁵`. -/
theorem kappa7chan211111ThetaExcess_eq
    (u u' : LayerLink N → G) :
    kappa7chan211111ThetaExcess ρ μG u u'
      = kappa7chan211111ThetaSum ρ μG u u'
        - 6 * ((thetaSupports (N := N)).card : ℝ)
          * realMoment ρ μG 2 * (e1 ρ μG) ^ 5 := by
  classical
  have hbase : ∀ S ∈ thetaSupports (N := N),
      ∑ _P ∈ S, (realMoment ρ μG 2 * (e1 ρ μG) ^ 5)
        = 6 * (realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
    intro S hS
    have hS6 : S.card = 6 := card_eq_six_of_mem_thetaSupports hS
    rw [Finset.sum_const, hS6, nsmul_eq_mul, Nat.cast_ofNat]
  have step1 : kappa7chan211111ThetaExcess ρ μG u u'
      = kappa7chan211111ThetaSum ρ μG u u'
        - ∑ S ∈ thetaSupports (N := N), ∑ _P ∈ S,
            (realMoment ρ μG 2 * (e1 ρ μG) ^ 5) := by
    unfold kappa7chan211111ThetaExcess kappa7chan211111ThetaSum
      kappa7chan211111Theta
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_sub_distrib _ _
  have step2 : (∑ S ∈ thetaSupports (N := N), ∑ _P ∈ S,
        (realMoment ρ μG 2 * (e1 ρ μG) ^ 5))
      = 6 * ((thetaSupports (N := N)).card : ℝ)
        * realMoment ρ μG 2 * (e1 ρ μG) ^ 5 := by
    rw [Finset.sum_congr rfl hbase, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [step1, step2]

/-- **The `(1⁷)` channel excess on the `Θ(1,3,3)` book
supports**: the book family channel sum with its
fully-split baseline `e₁⁷` removed summand by summand.
No sign is asserted for it. -/
noncomputable def kappa7chanTheta133Excess
    (u u' : LayerLink N → G) : ℝ :=
  ∑ S ∈ theta133Supports,
    (kappa7chanTheta133 ρ μG S u u' - (e1 ρ μG) ^ 7)

/-- The book `(1⁷)` channel excess is the raw family
channel sum minus its baseline: each book support
carries baseline `e₁⁷`. -/
theorem kappa7chanTheta133Excess_eq (u u' : LayerLink N → G) :
    kappa7chanTheta133Excess ρ μG u u'
      = kappa7chanTheta133Sum ρ μG u u'
        - ((theta133Supports (N := N)).card : ℝ)
          * (e1 ρ μG) ^ 7 := by
  classical
  have step1 : kappa7chanTheta133Excess ρ μG u u'
      = kappa7chanTheta133Sum ρ μG u u'
        - ∑ _S ∈ theta133Supports (N := N), (e1 ρ μG) ^ 7 := by
    unfold kappa7chanTheta133Excess kappa7chanTheta133Sum
    exact Finset.sum_sub_distrib _ _
  have step2 : (∑ _S ∈ theta133Supports (N := N), (e1 ρ μG) ^ 7)
      = ((theta133Supports (N := N)).card : ℝ)
        * (e1 ρ μG) ^ 7 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [step1, step2]

end Assembly7

/-! ## B7-2a close: what this brick owns, and the seam

This brick (B7-2a) owns: the `Θ(1,3,3)` book support
family; the three family channel sums deferred by
B7-1b; and the seven channel excesses of the β⁷ LIVE
list — `(4,1,1,1)`, `(3,2,1,1)`-ADJ, `(3,2,1,1)`-OPP
(with the unsplit `(3,2,1,1)` excess and the
split-sums-to-unsplit identity), `(2,2,2,1)`,
`(2,1,1,1,1,1)` on `C₆`, `(2,1,1,1,1,1)` on `Θ(2,2,2)`,
and `(1⁷)` on the book support — each with its baseline
bookkeeping proved above. The assembly identity
`kappa7dep_eq` is B7-2b's work, over the order-7 total
decomposition and the fiber accounting (B7-0's card-5
and card-6 erasure claims are settled there, by proof,
in whichever direction they fall); it is **not**
asserted in this brick. No sign is asserted for
`kappa7dep` or for any excess here: the β⁷ general
sign remains FRONTIER. NO CLAIM; parts of the Clay
Yang–Mills statement closed by this brick: 0; dials
0/4. -/

#print axioms kappa7chan4111Excess_eq
#print axioms kappa7chan3211Excess_eq
#print axioms kappa7chan3211AdjExcess_eq
#print axioms kappa7chan3211OppExcess_eq
#print axioms kappa7chan3211Adj_add_Opp_excess
#print axioms kappa7chan2221Excess_eq
#print axioms kappa7chan211111C6Excess_eq
#print axioms kappa7chan211111ThetaExcess_eq
#print axioms kappa7chanTheta133Excess_eq

end ThetLogos
