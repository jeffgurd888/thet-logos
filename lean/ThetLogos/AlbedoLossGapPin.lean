/-
# AlbedoLossGapPin — albedo loss vs the finite gap, on the slice seat

**Scope: ~/workspace/your_files/albedo-loss-vs-gap-scope-2026-11-21.md.
Commissioned by Zero, 2026-11-21 ("scope the finite version"), from
his seeing of the same night: "is gravity equal to total thermal
albedo loss." T5. NO CLAIM. Dial 2 stays 0 under every outcome.**

THE VERDICT ON THE SEEING AS POSED IS ALREADY GIVEN IN THE SCOPE
AND IS NOT RELITIGATED HERE: NO — (1) type: gravity (acceleration /
coupling G) and albedo loss (dimensionless fraction / radiative
flux) share no type and no conversion object exists in-tree;
(2) corpus: neither side exists as a corpus object; (3) physics:
albedo varies at fixed mass (mirror vs black shell) and gravity
does not change. This pin prices only the finite, stateable
residue: on the slice seat, where BOTH a thermal-albedo-loss
quantity and a gap quantity can be honestly defined, test what
relation — equality, bound, tracking, or countermodel — holds.

**K-ALB-NAME, pre-registered in the scope and standing over every
brick of this pin:** the finite gap in this pin is a finite graph
spectral quantity (the slice's Fiedler value). It may NOT be called
gravity anywhere in the pin — wearing the word "gravity" for the
finite gap is the rename failure, and it kills the brick it
appears in. No gravity object is defined here, no G is derived,
nothing continuum is stated. Dial 2 = 0.

**BRICK 0 — THE RECORD PIN (0 strict by design).** The frozen
definitions, pinned before any verdict is computed: the local
index, the Fresnel reflection split, the step convention, the
seat's albedo, its total thermal albedo loss, and the gap
citation. Definitions only — no theorem content to strike.
Per the scope's RTE-2 rule, these definitions may NOT be repaired
to force or soften an answer in later bricks; if a definition
proves unworkable, the pin stops and reports, it does not swap.

THE SEAT: `OrbifoldGapPin.Slice 2 0` — the equatorial diagonal
layer L₀ of the ball B₂ ⊂ ℤ³, 7 nodes, a hexagon with a centre —
with its nearest-neighbour weights `OrbifoldGapPin.sliceW`. The
landscape φ lives on the same 7 nodes, so no seat-bridge is
needed and none is smuggled in.

**THE LOCAL `refIndex` — COLLISION DISCLOSED ON THE FACE.** This
brick defines `ThetLogos.refIndex` as the Slice-specialized form
of the refractive index, reproducing verbatim the formula pinned
in RTE Brick 1 (`RefractiveThermalEntropyPin`, hb lane / main
tree): `refIndex w φ i = 1 + ∑ j, w i j * |φ i − φ j|`. The lane
tree carries no other `refIndex` (tree-wide grep: zero hits), so
the local def stands at lane grade. **T10 BLOCKING ITEM:** at
integration this local def COLLIDES with RTE's in-tree
`ThetLogos.refIndex`; the reconciliation on record is to DROP
this local def at integration and import RTE's, with `w` then
read as `sliceW` at every use below. Nothing in this brick's
content depends on which of the two identical formulas supplies
the index.

**RESOLVED AT T10 INTEGRATION (2026-11-22):** the local def is
dropped in this in-tree form and RTE's is imported, as prescribed
above. Companion item (INTEG-T10-STATE F-T10-3): this module's
flat-landscape theorem `refIndex_eq_one_of_forall_eq` shares its
name with RTE's different theorem of the same name (per-site
disjunction form); in this form it is renamed
`refIndex_eq_one_of_forall_eq_slice` — statement and proof
unchanged.

THE STEP CONVENTION (frozen here, part of Brick 0's definitions):
the incident distribution is the seat's Gibbs distribution at β
over the landscape φ (`ModularVariance.gibbsProb` — the thermal
reading of "thermal": the incident flux arrives as the seat's own
Gibbs weights distribute it). Each incident quantum at i steps to
a neighbour by the PLAIN weights, row-normalized:
`stepProb w i j = w i j / ∑ k, w i k` (a zero row gives 0 by the
field convention, as written). Of the step i → j, the Fresnel
fraction `reflFrac w φ i j` is reflected (turned back) and the
rest is absorbed (thermalized). **albedo** = total reflected /
total incident; **total thermal albedo loss** = 1 − albedo, the
seat-wide absorbed fraction.

K-ALB-EQ is armed for Brick 1 (the equality claim, expected to
DIE by the pre-registered mirror/black countermodel pair: fixed
graph, varied landscape). K-ALB-TRACK is armed for Brick 2.
Neither is approached in this brick.
-/

import ThetLogos.OrbifoldGapPin
import ThetLogos.ModularVariance
import ThetLogos.OrbifoldGapZF7
import ThetLogos.DuctGap
import ThetLogos.RefractiveThermalEntropyPin

namespace ThetLogos

/-- The slice seat is inhabited (its centre node), as the Gibbs
machinery requires. Registration only. -/
instance : Nonempty (OrbifoldGapPin.Slice 2 0) :=
  ⟨OrbifoldGapPin.centerNode⟩

/- **The refractive index on the slice seat** is RTE's
`ThetLogos.refIndex` (imported above from
`RefractiveThermalEntropyPin`), read at the Slice seat. At lane
grade a Slice-specialized local def stood here, verbatim-identical
in body (`refIndex w φ i = 1 + ∑ j, w i j * |φ i − φ j|`); it was
DROPPED at T10 integration per the header's collision disclosure,
and every use below now reads RTE's general def at
`V = OrbifoldGapPin.Slice 2 0`. -/

/-- **The Fresnel reflection fraction** (Brick 0 — frozen
definition): at an ordered pair (i, j) of slice nodes, the
reflected fraction of a step i → j is the Fresnel-form
coefficient of the index contrast,
`((refIndex w φ i − refIndex w φ j) / (refIndex w φ i + refIndex w φ j))²`.
The transmitted fraction is `1 − reflFrac w φ i j`. Flat
landscape ⇒ every index is 1 ⇒ contrast 0 ⇒ nothing reflects. -/
noncomputable def reflFrac (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (i j : OrbifoldGapPin.Slice 2 0) : ℝ :=
  ((refIndex w φ i - refIndex w φ j) / (refIndex w φ i + refIndex w φ j)) ^ 2

/-- **The step convention** (Brick 0 — frozen definition): from
i, an incident quantum steps to j with probability proportional
to the plain weight, row-normalized:
`stepProb w i j = w i j / ∑ k, w i k`. -/
noncomputable def stepProb (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (i j : OrbifoldGapPin.Slice 2 0) : ℝ :=
  w i j / ∑ k, w i k

/-- **Total incident flux** (Brick 0 — frozen definition): the
Gibbs mass of the incident distribution at β over φ. (It is 1 by
`ModularVariance.sum_gibbsProb`; the ratio below is kept explicit
so the albedo definition reads as stated in the scope.) -/
noncomputable def totalIncident (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (β : ℝ) : ℝ :=
  ∑ i, ModularVariance.gibbsProb φ β i

/-- **Total reflected flux** (Brick 0 — frozen definition): the
Gibbs-weighted seat total of the reflected fractions — each
incident quantum at i contributes its Gibbs weight times the
step-averaged Fresnel fraction over its steps out of i. -/
noncomputable def totalReflected (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (β : ℝ) : ℝ :=
  ∑ i, ModularVariance.gibbsProb φ β i * (∑ j, stepProb w i j * reflFrac w φ i j)

/-- **The seat's albedo** (Brick 0 — frozen definition): total
reflected / total incident. -/
noncomputable def seatAlbedo (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (β : ℝ) : ℝ :=
  totalReflected w φ β / totalIncident φ β

/-- **Total thermal albedo loss** (Brick 0 — frozen definition):
`1 − albedo` — the seat-wide absorbed fraction. A dimensionless
fraction of a finite seat's Gibbs-distributed incident flux. It
is not gravity, not an acceleration, not a coupling; K-ALB-NAME
stands over this name and every use of it. -/
noncomputable def totalThermalAlbedoLoss
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (β : ℝ) : ℝ :=
  1 - seatAlbedo w φ β

/-- **The gap citation** (Brick 0 — frozen definition): the
slice graph's Fiedler value at R = 2, `fiedler sliceW` — a
finite graph spectral quantity of the weight field alone, via
the in-tree Bridge Fiedler package. NOT gravity (K-ALB-NAME);
Dial 2 stays 0. -/
noncomputable def sliceFiedlerGap : ℝ :=
  fiedler (OrbifoldGapPin.sliceW (R := 2) (h := 0))

/-! ## Brick 1 — the closed form + the equality kill

**K-ALB-EQ FIRES IN THIS BRICK**, by the pre-registered
countermodel pair, exactly as priced in the scope (T1): FIX the
weight field at `sliceW`, so `sliceFiedlerGap` is one fixed
number, and vary the landscape. The flat landscape has loss
exactly 1 — total loss, albedo 0 (`totalThermalAlbedoLoss_of_
forall_eq`). The sharp-contrast landscape `sharpLandscape`
(value 1 at the centre node, 0 on the rim) has indices 7 at the
centre and 2 at the rim node (1, −1, 0) — interface Fresnel
fraction ((7 − 2)/(7 + 2))² = 25/81 > 0 — so some incident flux
reflects at every β and its loss is strictly less than 1
(`totalThermalAlbedoLoss_sharp_lt_one`). Equal gap, different
loss: the seat's total thermal albedo loss is NOT determined by
its gap — `albedoLoss_not_determined_by_gap`. The closed forms
banked alongside: a constant landscape has index 1 everywhere,
and a two-level landscape's index and Fresnel fraction factor
through the landscape's index contrast and its boundary weights
alone (`refIndex_two_level`, `reflFrac_two_level`). NO CLAIM.
The finite gap is a graph spectral quantity, not gravity
(K-ALB-NAME); Dial 2 stays 0. K-ALB-TRACK remains armed for
Brick 2 and is not touched here. -/

/-- **The sharp-contrast landscape** (Brick 1): value 1 at the
centre node — the unique slice node with coordinates (0, 0, 0) —
and 0 on the rim. The countermodel's second landscape: maximal
index contrast at the hub interface, against the flat
landscape's none. -/
noncomputable def sharpLandscape (q : OrbifoldGapPin.Slice 2 0) : ℝ :=
  if q.1 = (0, 0, 0) then 1 else 0

/-- **Flat ⇒ index 1** (Brick 1): a landscape whose values all
agree has refractive index exactly 1 at every node — the local
gradient vanishes everywhere. -/
theorem refIndex_eq_one_of_forall_eq_slice
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (hφ : ∀ i j, φ i = φ j)
    (i : OrbifoldGapPin.Slice 2 0) : refIndex w φ i = 1 := by
  have hterm : ∀ j, w i j * |φ i - φ j| = 0 := by
    intro j
    rw [hφ i j, sub_self, abs_zero, mul_zero]
  unfold refIndex
  rw [Finset.sum_eq_zero (fun j _ => hterm j), add_zero]

/-- **The flat landscape's loss is total** (Brick 1): if the
landscape's values all agree, every index is 1, every Fresnel
fraction is 0, nothing reflects — albedo 0, total thermal
albedo loss exactly 1, at every weight field and every β. -/
theorem totalThermalAlbedoLoss_of_forall_eq
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (β : ℝ) (hφ : ∀ i j, φ i = φ j) :
    totalThermalAlbedoLoss w φ β = 1 := by
  have hrefl : ∀ i j, reflFrac w φ i j = 0 := by
    intro i j
    unfold reflFrac
    rw [refIndex_eq_one_of_forall_eq_slice w φ hφ i,
      refIndex_eq_one_of_forall_eq_slice w φ hφ j]
    norm_num
  have hTR : totalReflected w φ β = 0 := by
    unfold totalReflected
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Finset.sum_eq_zero (fun j _ => by rw [hrefl i j, mul_zero]),
      mul_zero]
  unfold totalThermalAlbedoLoss seatAlbedo
  rw [hTR, zero_div, sub_zero]

/-- **The two-level index closed form** (Brick 1): if the
landscape takes only the two values `a` and `b`, the index at
`i` factors through the contrast alone: `1 + |a − b|` times the
total weight from `i` into the opposite level. The loss side of
the seat reads the landscape only through this contrast and
these boundary weights. -/
theorem refIndex_two_level
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (a b : ℝ)
    (hφ : ∀ i, φ i = a ∨ φ i = b) (i : OrbifoldGapPin.Slice 2 0) :
    refIndex w φ i
      = 1 + |a - b| * ∑ j ∈ Finset.univ.filter (fun j => φ j ≠ φ i),
          w i j := by
  classical
  have hterm : ∀ j ∈ Finset.univ.filter (fun j => φ j ≠ φ i),
      w i j * |φ i - φ j| = w i j * |a - b| := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hji : φ j ≠ φ i := hj.2
    rcases hφ i with hi | hi <;> rcases hφ j with hjv | hjv
    · exact absurd (hjv.trans hi.symm) hji
    · rw [hi, hjv]
    · rw [hi, hjv, abs_sub_comm]
    · exact absurd (hjv.trans hi.symm) hji
  have hzero : ∀ j ∈ Finset.univ.filter (fun j => ¬ φ j ≠ φ i),
      w i j * |φ i - φ j| = 0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjeq : φ j = φ i := not_not.mp hj.2
    rw [← hjeq, sub_self, abs_zero, mul_zero]
  have hswap : ∀ j ∈ Finset.univ.filter (fun j => φ j ≠ φ i),
      w i j * |a - b| = |a - b| * w i j :=
    fun j _ => mul_comm _ _
  unfold refIndex
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => φ j ≠ φ i) (fun j => w i j * |φ i - φ j|),
    Finset.sum_congr rfl hterm, Finset.sum_congr rfl hzero,
    Finset.sum_const_zero, add_zero, Finset.sum_congr rfl hswap,
    ← Finset.mul_sum]

/-- **The two-level Fresnel closed form** (Brick 1): for a
two-level landscape, the reflected fraction of a step `i → j`
is the Fresnel coefficient of the two indices, with the indices
themselves replaced by their closed forms — the fraction
depends on the landscape only through the contrast `|a − b|`
and the two nodes' boundary weights into their opposite
levels. -/
theorem reflFrac_two_level
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (a b : ℝ)
    (hφ : ∀ i, φ i = a ∨ φ i = b)
    (i j : OrbifoldGapPin.Slice 2 0) :
    reflFrac w φ i j
      = ((|a - b| * ((∑ k ∈ Finset.univ.filter (fun k => φ k ≠ φ i),
              w i k)
            - (∑ k ∈ Finset.univ.filter (fun k => φ k ≠ φ j),
              w j k)))
        / (2 + |a - b| * ((∑ k ∈ Finset.univ.filter
              (fun k => φ k ≠ φ i), w i k)
            + (∑ k ∈ Finset.univ.filter (fun k => φ k ≠ φ j),
              w j k)))) ^ 2 := by
  classical
  unfold reflFrac
  rw [refIndex_two_level w φ a b hφ i, refIndex_two_level w φ a b hφ j]
  congr 1
  congr 1 <;> ring

/-- **The sharp landscape's index at the centre is 7** (Brick
1): the centre is adjacent to all six rim nodes, each at
contrast 1, so its index is `1 + 6`. Computed on the explicit
seven-node layer (ZF-7's evaluation pattern). -/
theorem refIndex_sharp_centerNode :
    refIndex OrbifoldGapPin.sliceW sharpLandscape
      OrbifoldGapPin.centerNode = 7 := by
  have hsum : (∑ j, OrbifoldGapPin.sliceW OrbifoldGapPin.centerNode j
      * |sharpLandscape OrbifoldGapPin.centerNode
        - sharpLandscape j|) = 6 := by
    calc (∑ j, OrbifoldGapPin.sliceW OrbifoldGapPin.centerNode j
          * |sharpLandscape OrbifoldGapPin.centerNode - sharpLandscape j|)
        = ∑ j, (if (OrbifoldGapPin.centerNode.1.1 - j.1.1) ^ 2
              + (OrbifoldGapPin.centerNode.1.2.1 - j.1.2.1) ^ 2
              + (OrbifoldGapPin.centerNode.1.2.2 - j.1.2.2) ^ 2 = 2
            then (1 : ℝ) else 0)
            * |(1 : ℝ) - (if j.1 = (0, 0, 0) then (1 : ℝ) else 0)| :=
          Finset.sum_congr rfl (fun j _ => rfl)
      _ = ∑ t ∈ OrbifoldGapPin.layerFinset 2 0,
            (if (OrbifoldGapPin.centerNode.1.1 - t.1) ^ 2
              + (OrbifoldGapPin.centerNode.1.2.1 - t.2.1) ^ 2
              + (OrbifoldGapPin.centerNode.1.2.2 - t.2.2) ^ 2 = 2
            then (1 : ℝ) else 0)
            * |(1 : ℝ) - (if t = (0, 0, 0) then (1 : ℝ) else 0)| :=
          Finset.sum_coe_sort (OrbifoldGapPin.layerFinset 2 0)
            (fun t : ℤ × ℤ × ℤ =>
              (if (OrbifoldGapPin.centerNode.1.1 - t.1) ^ 2
                + (OrbifoldGapPin.centerNode.1.2.1 - t.2.1) ^ 2
                + (OrbifoldGapPin.centerNode.1.2.2 - t.2.2) ^ 2 = 2
              then (1 : ℝ) else 0)
              * |(1 : ℝ) - (if t = (0, 0, 0) then (1 : ℝ) else 0)|)
      _ = ∑ t ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
            (-1, 1, 0), (1, 0, -1), (0, -1, 1)} :
            Finset (ℤ × ℤ × ℤ)),
            (if (OrbifoldGapPin.centerNode.1.1 - t.1) ^ 2
              + (OrbifoldGapPin.centerNode.1.2.1 - t.2.1) ^ 2
              + (OrbifoldGapPin.centerNode.1.2.2 - t.2.2) ^ 2 = 2
            then (1 : ℝ) else 0)
            * |(1 : ℝ) - (if t = (0, 0, 0) then (1 : ℝ) else 0)| :=
          Finset.sum_congr OrbifoldGapPin.layerFinset_two_zero
            (fun t _ => rfl)
      _ = 6 := by
          norm_num [Finset.sum_insert, Finset.sum_singleton,
            OrbifoldGapPin.centerNode, OrbifoldGapPin.rimANode]
  unfold refIndex
  rw [hsum]
  norm_num

/-- **The sharp landscape's index at the rim node (1, −1, 0) is
2** (Brick 1): of the rim node's three neighbours, only the
centre sits at the opposite level, with weight 1, so its index
is `1 + 1`. Computed on the explicit seven-node layer. -/
theorem refIndex_sharp_rimANode :
    refIndex OrbifoldGapPin.sliceW sharpLandscape
      OrbifoldGapPin.rimANode = 2 := by
  have hsum : (∑ j, OrbifoldGapPin.sliceW OrbifoldGapPin.rimANode j
      * |sharpLandscape OrbifoldGapPin.rimANode
        - sharpLandscape j|) = 1 := by
    calc (∑ j, OrbifoldGapPin.sliceW OrbifoldGapPin.rimANode j
          * |sharpLandscape OrbifoldGapPin.rimANode - sharpLandscape j|)
        = ∑ j, (if (OrbifoldGapPin.rimANode.1.1 - j.1.1) ^ 2
              + (OrbifoldGapPin.rimANode.1.2.1 - j.1.2.1) ^ 2
              + (OrbifoldGapPin.rimANode.1.2.2 - j.1.2.2) ^ 2 = 2
            then (1 : ℝ) else 0)
            * |(0 : ℝ) - (if j.1 = (0, 0, 0) then (1 : ℝ) else 0)| :=
          Finset.sum_congr rfl (fun j _ => rfl)
      _ = ∑ t ∈ OrbifoldGapPin.layerFinset 2 0,
            (if (OrbifoldGapPin.rimANode.1.1 - t.1) ^ 2
              + (OrbifoldGapPin.rimANode.1.2.1 - t.2.1) ^ 2
              + (OrbifoldGapPin.rimANode.1.2.2 - t.2.2) ^ 2 = 2
            then (1 : ℝ) else 0)
            * |(0 : ℝ) - (if t = (0, 0, 0) then (1 : ℝ) else 0)| :=
          Finset.sum_coe_sort (OrbifoldGapPin.layerFinset 2 0)
            (fun t : ℤ × ℤ × ℤ =>
              (if (OrbifoldGapPin.rimANode.1.1 - t.1) ^ 2
                + (OrbifoldGapPin.rimANode.1.2.1 - t.2.1) ^ 2
                + (OrbifoldGapPin.rimANode.1.2.2 - t.2.2) ^ 2 = 2
              then (1 : ℝ) else 0)
              * |(0 : ℝ) - (if t = (0, 0, 0) then (1 : ℝ) else 0)|)
      _ = ∑ t ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
            (-1, 1, 0), (1, 0, -1), (0, -1, 1)} :
            Finset (ℤ × ℤ × ℤ)),
            (if (OrbifoldGapPin.rimANode.1.1 - t.1) ^ 2
              + (OrbifoldGapPin.rimANode.1.2.1 - t.2.1) ^ 2
              + (OrbifoldGapPin.rimANode.1.2.2 - t.2.2) ^ 2 = 2
            then (1 : ℝ) else 0)
            * |(0 : ℝ) - (if t = (0, 0, 0) then (1 : ℝ) else 0)| :=
          Finset.sum_congr OrbifoldGapPin.layerFinset_two_zero
            (fun t _ => rfl)
      _ = 1 := by
          norm_num [Finset.sum_insert, Finset.sum_singleton,
            OrbifoldGapPin.centerNode, OrbifoldGapPin.rimANode]
  unfold refIndex
  rw [hsum]
  norm_num

/-- **The sharp landscape reflects** (Brick 1): at every β the
seat's total reflected flux under `sharpLandscape` is strictly
positive — the centre's own Gibbs weight rides a step to the
rim whose Fresnel fraction is ((7 − 2)/(7 + 2))² = 25/81 > 0,
and every term of the total is nonnegative. -/
theorem totalReflected_sharp_pos (β : ℝ) :
    0 < totalReflected OrbifoldGapPin.sliceW sharpLandscape β := by
  have hsliceWcr : OrbifoldGapPin.sliceW OrbifoldGapPin.centerNode
      OrbifoldGapPin.rimANode = 1 := by
    norm_num [OrbifoldGapPin.sliceW, OrbifoldGapPin.centerNode,
      OrbifoldGapPin.rimANode]
  have hrowsum : (0 : ℝ) < ∑ k, OrbifoldGapPin.sliceW
      OrbifoldGapPin.centerNode k := by
    have hle := Finset.single_le_sum
      (fun k _ => OrbifoldGapPin.sliceW_nonneg
        OrbifoldGapPin.centerNode k)
      (Finset.mem_univ OrbifoldGapPin.rimANode)
    rw [hsliceWcr] at hle
    exact one_pos.trans_le hle
  have hsp : 0 < stepProb OrbifoldGapPin.sliceW
      OrbifoldGapPin.centerNode OrbifoldGapPin.rimANode := by
    unfold stepProb
    rw [hsliceWcr]
    exact div_pos one_pos hrowsum
  have hrefl : 0 < reflFrac OrbifoldGapPin.sliceW sharpLandscape
      OrbifoldGapPin.centerNode OrbifoldGapPin.rimANode := by
    unfold reflFrac
    rw [refIndex_sharp_centerNode, refIndex_sharp_rimANode]
    norm_num
  have hstep_nn : ∀ i j, 0 ≤ stepProb OrbifoldGapPin.sliceW i j := by
    intro i j
    unfold stepProb
    exact div_nonneg (OrbifoldGapPin.sliceW_nonneg i j)
      (Finset.sum_nonneg (fun k _ => OrbifoldGapPin.sliceW_nonneg i k))
  have hrefl_nn : ∀ i j, 0 ≤ reflFrac OrbifoldGapPin.sliceW
      sharpLandscape i j := by
    intro i j
    unfold reflFrac
    positivity
  have hinner : 0 < ∑ j, stepProb OrbifoldGapPin.sliceW
      OrbifoldGapPin.centerNode j
      * reflFrac OrbifoldGapPin.sliceW sharpLandscape
        OrbifoldGapPin.centerNode j := by
    refine lt_of_lt_of_le (mul_pos hsp hrefl) ?_
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg
        (hstep_nn OrbifoldGapPin.centerNode j)
        (hrefl_nn OrbifoldGapPin.centerNode j))
      (Finset.mem_univ OrbifoldGapPin.rimANode)
  unfold totalReflected
  refine Finset.sum_pos' (fun i _ => mul_nonneg
    (ModularVariance.gibbsProb_pos sharpLandscape β i).le
    (Finset.sum_nonneg (fun j _ => mul_nonneg (hstep_nn i j)
      (hrefl_nn i j)))) ?_
  exact ⟨OrbifoldGapPin.centerNode, Finset.mem_univ _,
    mul_pos (ModularVariance.gibbsProb_pos sharpLandscape β
      OrbifoldGapPin.centerNode) hinner⟩

/-- **The sharp landscape's loss is not total** (Brick 1): at
every β, `totalThermalAlbedoLoss sliceW sharpLandscape β < 1`
— the seat absorbs strictly less than everything, because some
flux reflects at the hub interface. The countermodel's second
half. -/
theorem totalThermalAlbedoLoss_sharp_lt_one (β : ℝ) :
    totalThermalAlbedoLoss OrbifoldGapPin.sliceW sharpLandscape β
      < 1 := by
  have hTI : totalIncident sharpLandscape β = 1 :=
    ModularVariance.sum_gibbsProb sharpLandscape β
  have hpos := totalReflected_sharp_pos β
  unfold totalThermalAlbedoLoss seatAlbedo
  rw [hTI, div_one]
  linarith

/-- **K-ALB-EQ — FIRED (Brick 1).** The seat's total thermal
albedo loss is NOT determined by its gap: there is no function
of `sliceFiedlerGap` that returns the loss for every landscape
and every β. The gap is a function of the weight field alone;
at the fixed weight field `sliceW` the flat landscape's loss
is exactly 1 while the sharp-contrast landscape's loss is
strictly less than 1 — equal gap, different loss, by
exhibition, the finite mirror/black pair of the scope. The
loss reads the landscape; the gap reads the weight field;
neither is the other. (The gap is a finite graph spectral
quantity — it is not gravity; K-ALB-NAME. Dial 2 stays 0.) -/
theorem albedoLoss_not_determined_by_gap :
    ¬ ∃ f : ℝ → ℝ, ∀ (φ : OrbifoldGapPin.Slice 2 0 → ℝ) (β : ℝ),
      totalThermalAlbedoLoss OrbifoldGapPin.sliceW φ β
        = f sliceFiedlerGap := by
  rintro ⟨f, hf⟩
  have hflat := hf (fun _ => 0) 1
  have hsharp := hf sharpLandscape 1
  rw [totalThermalAlbedoLoss_of_forall_eq OrbifoldGapPin.sliceW
    (fun _ => 0) 1 (fun i j => rfl)] at hflat
  have hlt := totalThermalAlbedoLoss_sharp_lt_one 1
  linarith

/-! ## Brick 2 — tracking + the surviving partial

**K-ALB-TRACK IS DECIDED IN THIS BRICK, reported as found:
ANTI-TRACKING on the pre-registered scaling family.** The test
family is uniform weight scaling `w ↦ c·w`. The computation,
in three parts. (1) The step convention is scale-INVARIANT:
the row normalization cancels every `c ≠ 0`
(`stepProb_smul`). (2) The gap scales exactly: the Fiedler
value of the scaled field is `c` times the Fiedler value
(`fiedler_smul` — the admissible energies scale, and the
infimum of the scaled set is the scaled infimum), and the
slice's gap is strictly positive (`sliceFiedlerGap_pos`), so
on the family the gap is a strictly increasing ray through
the origin. (3) The loss side reads the index, and the index
is AFFINE in the scale — `refIndex (c·w) φ i = 1 + c·(the
unscaled sum)` (`refIndex_smul`): the leading `1` does not
scale, exactly as the scope flagged. The Fresnel fraction at
every interface is therefore nondecreasing in `c`
(`reflFrac_smul_le`), and at the sharp landscape's hub
interface it strictly increases — the fraction there is
`((5c)/(2 + 7c))²`, `25/81` at `c = 1` against `25/64` at
`c = 2`. Since the step convention does not move, the seat's
reflected total strictly increases and its loss strictly
DEcreases from scale 1 to scale 2 at every β
(`totalThermalAlbedoLoss_two_smul_sharp_lt`). Packaged:
`albedoLoss_antitracks_gap_scaling` — at scale 2 the gap has
doubled while the sharp landscape's loss has strictly fallen.
The loss does not track the gap on the scaling family; it
moves against it. **K-ALB-TRACK FIRES as anti-tracking.**

**The converse countermodel (T1's reverse pair, cheap as
priced).** The flat landscape's loss is exactly 1 at EVERY
weight field (Brick 1), hence at every scale — while the gap
takes the distinct values `0` (scale 0) and the slice's
positive gap (scale 1) there. So the gap is not determined
by the loss either: `gap_not_determined_by_loss`.

**The surviving partial (T3), in its labeled form:**
`albedo_gap_independence`. What stands after both kills is
the independence of the pair (gap, loss) over the seat
family, in three clauses: at fixed weights the loss varies
with the landscape (1 flat, < 1 sharp — Brick 1); at fixed
(flat) loss the gap varies with the scale; and on the
scaling family the two move in opposite directions. The gap
reads the weight field; the loss reads the landscape through
its index contrast (Brick 1's closed forms); neither is a
function of the other, in either direction. That independence
is the pin's positive theorem — the honest finite residue of
the seeing. NO CLAIM. The finite gap is a graph spectral
quantity, not gravity (K-ALB-NAME); no gravity object is
defined here, no G is derived, nothing continuum is stated.
Dial 2 stays 0. Definitions as frozen in Brick 0 — no
repairs were made or needed. -/

/-- **The step convention is scale-invariant** (Brick 2): for
`c ≠ 0`, row-normalizing the scaled weights `c·w` gives the
same step probabilities as row-normalizing `w` — the factor
cancels between numerator and row sum. On the scaling family
the step side of the seat does not move at all. -/
theorem stepProb_smul
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (c : ℝ) (hc : c ≠ 0) (i j : OrbifoldGapPin.Slice 2 0) :
    stepProb (fun i j => c * w i j) i j = stepProb w i j := by
  unfold stepProb
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- **The index is affine in the scale** (Brick 2):
`refIndex (c·w) φ i = 1 + c · (∑ j, w i j * |φ i − φ j|)` —
the sum scales, the leading `1` does not. This is the whole
mechanism of the tracking verdict: the index is not a
homogeneous function of the weight field, so the Fresnel
fractions built from it are not scale-invariant even though
the step convention is. -/
theorem refIndex_smul
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (c : ℝ) (φ : OrbifoldGapPin.Slice 2 0 → ℝ)
    (i : OrbifoldGapPin.Slice 2 0) :
    refIndex (fun i j => c * w i j) φ i
      = 1 + c * (∑ j, w i j * |φ i - φ j|) := by
  unfold refIndex
  show 1 + ∑ j, c * w i j * |φ i - φ j|
    = 1 + c * ∑ j, w i j * |φ i - φ j|
  have hterm : ∀ j : OrbifoldGapPin.Slice 2 0,
      c * w i j * |φ i - φ j| = c * (w i j * |φ i - φ j|) :=
    fun j => mul_assoc c (w i j) |φ i - φ j|
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]

/-- **The Fresnel fraction is nondecreasing in the scale**
(Brick 2): for nonnegative weights, at every ordered pair
`(i, j)` and every landscape, scaling the weights by a
larger positive factor cannot decrease the reflected
fraction. In closed form the fraction at scale `c` is
`((c·(sᵢ − sⱼ)) / (2 + c·(sᵢ + sⱼ)))²` with `s` the unscaled
index sum, and `c ↦ c/(2 + c·t)` is nondecreasing for
`t ≥ 0`. -/
theorem reflFrac_smul_le
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (φ : OrbifoldGapPin.Slice 2 0 → ℝ)
    (c₁ c₂ : ℝ) (hc1 : 0 < c₁) (hc12 : c₁ ≤ c₂)
    (i j : OrbifoldGapPin.Slice 2 0) :
    reflFrac (fun i j => c₁ * w i j) φ i j
      ≤ reflFrac (fun i j => c₂ * w i j) φ i j := by
  have hs_i : 0 ≤ ∑ j, w i j * |φ i - φ j| :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hw i j) (abs_nonneg _))
  have hs_j : 0 ≤ ∑ k, w j k * |φ j - φ k| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hw j k) (abs_nonneg _))
  have hform : ∀ c : ℝ, reflFrac (fun i j => c * w i j) φ i j
      = ((c * ((∑ j, w i j * |φ i - φ j|)
            - (∑ k, w j k * |φ j - φ k|)))
        / (2 + c * ((∑ j, w i j * |φ i - φ j|)
            + (∑ k, w j k * |φ j - φ k|)))) ^ 2 := by
    intro c
    unfold reflFrac
    simp only [refIndex_smul]
    congr 1
    congr 1 <;> ring
  rw [hform c₁, hform c₂]
  set d := (∑ j, w i j * |φ i - φ j|)
    - (∑ k, w j k * |φ j - φ k|) with hd_def
  set t := (∑ j, w i j * |φ i - φ j|)
    + (∑ k, w j k * |φ j - φ k|) with ht_def
  have ht : 0 ≤ t := by
    rw [ht_def]
    exact add_nonneg hs_i hs_j
  have hd1 : (0:ℝ) < 2 + c₁ * t := by
    linarith [mul_nonneg hc1.le ht]
  have hd2 : (0:ℝ) < 2 + c₂ * t := by
    linarith [mul_nonneg (le_trans hc1.le hc12) ht]
  have habs : |(c₁ * d) / (2 + c₁ * t)| ≤ |(c₂ * d) / (2 + c₂ * t)| := by
    rw [abs_div, abs_div, abs_of_pos hd1, abs_of_pos hd2, abs_mul, abs_mul,
      abs_of_pos hc1, abs_of_pos (lt_of_lt_of_le hc1 hc12),
      div_le_div_iff₀ hd1 hd2]
    nlinarith [mul_nonneg (abs_nonneg d) (sub_nonneg.mpr hc12),
      mul_nonneg (mul_nonneg (abs_nonneg d) ht)
        (mul_nonneg hc1.le (le_trans hc1.le hc12))]
  calc ((c₁ * d) / (2 + c₁ * t)) ^ 2
      = |(c₁ * d) / (2 + c₁ * t)| ^ 2 := (sq_abs _).symm
    _ ≤ |(c₂ * d) / (2 + c₂ * t)| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = ((c₂ * d) / (2 + c₂ * t)) ^ 2 := sq_abs _

/-- **The sharp landscape's loss strictly falls from scale 1
to scale 2** (Brick 2): at every β,
`totalThermalAlbedoLoss (2·sliceW) sharpLandscape β
< totalThermalAlbedoLoss sliceW sharpLandscape β`.
The step convention is scale-invariant, every interface's
Fresnel fraction is nondecreasing in the scale, and the hub
interface's fraction strictly increases — its closed form
`((5c)/(2 + 7c))²` is `25/81` at `c = 1` and `25/64` at
`c = 2` — on a step of positive probability under a positive
Gibbs weight; so the reflected total strictly increases and
the loss, its complement, strictly falls. -/
theorem totalThermalAlbedoLoss_two_smul_sharp_lt (β : ℝ) :
    totalThermalAlbedoLoss (fun i j => (2:ℝ) * OrbifoldGapPin.sliceW i j)
        sharpLandscape β
      < totalThermalAlbedoLoss OrbifoldGapPin.sliceW sharpLandscape β := by
  classical
  have h1w : (fun i j : OrbifoldGapPin.Slice 2 0 =>
      (1:ℝ) * OrbifoldGapPin.sliceW i j) = OrbifoldGapPin.sliceW :=
    funext fun i => funext fun j => one_mul _
  have hs6 : (∑ j, OrbifoldGapPin.sliceW OrbifoldGapPin.centerNode j
      * |sharpLandscape OrbifoldGapPin.centerNode
        - sharpLandscape j|) = 6 := by
    have h := refIndex_sharp_centerNode
    unfold refIndex at h
    linarith
  have hs1 : (∑ j, OrbifoldGapPin.sliceW OrbifoldGapPin.rimANode j
      * |sharpLandscape OrbifoldGapPin.rimANode
        - sharpLandscape j|) = 1 := by
    have h := refIndex_sharp_rimANode
    unfold refIndex at h
    linarith
  have hsp_nn : ∀ i j, 0 ≤ stepProb OrbifoldGapPin.sliceW i j := by
    intro i j
    unfold stepProb
    exact div_nonneg (OrbifoldGapPin.sliceW_nonneg i j)
      (Finset.sum_nonneg (fun k _ => OrbifoldGapPin.sliceW_nonneg i k))
  have hsp_pos : 0 < stepProb OrbifoldGapPin.sliceW
      OrbifoldGapPin.centerNode OrbifoldGapPin.rimANode := by
    have hsliceWcr : OrbifoldGapPin.sliceW OrbifoldGapPin.centerNode
        OrbifoldGapPin.rimANode = 1 := by
      norm_num [OrbifoldGapPin.sliceW, OrbifoldGapPin.centerNode,
        OrbifoldGapPin.rimANode]
    have hrowsum : (0:ℝ) < ∑ k, OrbifoldGapPin.sliceW
        OrbifoldGapPin.centerNode k := by
      have hle := Finset.single_le_sum
        (fun k _ => OrbifoldGapPin.sliceW_nonneg
          OrbifoldGapPin.centerNode k)
        (Finset.mem_univ OrbifoldGapPin.rimANode)
      rw [hsliceWcr] at hle
      exact one_pos.trans_le hle
    unfold stepProb
    rw [hsliceWcr]
    exact div_pos one_pos hrowsum
  have hform : ∀ c : ℝ,
      reflFrac (fun i j => c * OrbifoldGapPin.sliceW i j) sharpLandscape
        OrbifoldGapPin.centerNode OrbifoldGapPin.rimANode
        = ((5 * c) / (2 + 7 * c)) ^ 2 := by
    intro c
    unfold reflFrac
    simp only [refIndex_smul]
    rw [hs6, hs1]
    congr 1
    congr 1 <;> ring
  have hstrict : reflFrac (fun i j => (1:ℝ) * OrbifoldGapPin.sliceW i j)
        sharpLandscape OrbifoldGapPin.centerNode OrbifoldGapPin.rimANode
      < reflFrac (fun i j => (2:ℝ) * OrbifoldGapPin.sliceW i j)
        sharpLandscape OrbifoldGapPin.centerNode
        OrbifoldGapPin.rimANode := by
    rw [hform 1, hform 2]
    norm_num
  have hTRform : ∀ (c : ℝ), c ≠ 0 →
      totalReflected (fun i j => c * OrbifoldGapPin.sliceW i j)
          sharpLandscape β
        = ∑ i, ModularVariance.gibbsProb sharpLandscape β i
          * (∑ j, stepProb OrbifoldGapPin.sliceW i j
            * reflFrac (fun i j => c * OrbifoldGapPin.sliceW i j)
              sharpLandscape i j) := by
    intro c hc
    unfold totalReflected
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by
      rw [stepProb_smul _ c hc i j])
  have hTR : totalReflected (fun i j => (1:ℝ) * OrbifoldGapPin.sliceW i j)
        sharpLandscape β
      < totalReflected (fun i j => (2:ℝ) * OrbifoldGapPin.sliceW i j)
        sharpLandscape β := by
    rw [hTRform 1 (by norm_num), hTRform 2 (by norm_num)]
    refine Finset.sum_lt_sum (fun i _ => ?_)
      ⟨OrbifoldGapPin.centerNode, Finset.mem_univ _, ?_⟩
    · exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (reflFrac_smul_le _ OrbifoldGapPin.sliceW_nonneg _ 1 2
            (by norm_num) (by norm_num) i j) (hsp_nn i j)))
        (ModularVariance.gibbsProb_pos sharpLandscape β i).le
    · refine mul_lt_mul_of_pos_left ?_
        (ModularVariance.gibbsProb_pos sharpLandscape β
          OrbifoldGapPin.centerNode)
      refine Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left
        (reflFrac_smul_le _ OrbifoldGapPin.sliceW_nonneg _ 1 2
          (by norm_num) (by norm_num) OrbifoldGapPin.centerNode j)
        (hsp_nn OrbifoldGapPin.centerNode j))
        ⟨OrbifoldGapPin.rimANode, Finset.mem_univ _, ?_⟩
      exact mul_lt_mul_of_pos_left hstrict hsp_pos
  rw [h1w] at hTR
  have hTI : totalIncident sharpLandscape β = 1 :=
    ModularVariance.sum_gibbsProb sharpLandscape β
  unfold totalThermalAlbedoLoss seatAlbedo
  rw [hTI, div_one, div_one]
  linarith

open scoped Pointwise in
/-- **The gap scales exactly** (Brick 2): for `c ≥ 0`, the
Fiedler value of the scaled weight field is `c` times the
Fiedler value of the field. The admissible energies scale
(the Laplacian is linear in the weights), so the admissible
set scales, and for `c ≥ 0` the infimum of the scaled set is
the scaled infimum. No hypothesis on `w` is needed — the
identity is pure set algebra over the variational
definition. -/
theorem fiedler_smul
    (w : OrbifoldGapPin.Slice 2 0 → OrbifoldGapPin.Slice 2 0 → ℝ)
    (c : ℝ) (hc : 0 ≤ c) :
    fiedler (fun i j => c * w i j) = c * fiedler w := by
  have henergy : ∀ F : OrbifoldGapPin.Slice 2 0 → ℝ,
      (∑ i, F i * laplacianOp (fun i j => c * w i j) F i)
        = c * ∑ i, F i * laplacianOp w F i := by
    intro F
    have hpt : ∀ i, laplacianOp (fun i j => c * w i j) F i
        = c * laplacianOp w F i := by
      intro i
      unfold laplacianOp
      show ∑ j, c * w i j * (F i - F j)
        = c * ∑ j, w i j * (F i - F j)
      have hterm : ∀ j : OrbifoldGapPin.Slice 2 0,
          c * w i j * (F i - F j) = c * (w i j * (F i - F j)) :=
        fun j => mul_assoc c (w i j) (F i - F j)
      rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
    calc (∑ i, F i * laplacianOp (fun i j => c * w i j) F i)
        = ∑ i, c * (F i * laplacianOp w F i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hpt i]; ring
      _ = c * ∑ i, F i * laplacianOp w F i := by
          rw [Finset.mul_sum]
  have hset : fiedlerSet (fun i j => c * w i j) = c • fiedlerSet w := by
    ext x
    constructor
    · rintro ⟨F, h0, h1, rfl⟩
      rw [Set.mem_smul_set]
      exact ⟨∑ i, F i * laplacianOp w F i, ⟨F, h0, h1, rfl⟩, by
        rw [smul_eq_mul]; exact (henergy F).symm⟩
    · rintro ⟨y, ⟨F, h0, h1, rfl⟩, rfl⟩
      show c • (∑ i, F i * laplacianOp w F i)
        ∈ fiedlerSet (fun i j => c * w i j)
      exact ⟨F, h0, h1, by
        rw [smul_eq_mul]; exact (henergy F).symm⟩
  rw [fiedler_def, hset, Real.sInf_smul_of_nonneg hc, fiedler_def,
    smul_eq_mul]

/-- **The slice's gap is strictly positive** (Brick 2):
`0 < sliceFiedlerGap`. The variational infimum is attained
(`fiedler_attained`, DuctGap); were the gap 0, the attaining
potential would have zero energy, hence would agree across
every conducting edge — and every rim node conducts to the
centre (weight exactly 1), so the potential would be
constant, contradicting mean-zero unit-norm on a 7-node
seat. The slice graph is connected through its hub, and the
gap feels it. -/
theorem sliceFiedlerGap_pos : 0 < sliceFiedlerGap := by
  show (0:ℝ) < fiedler (OrbifoldGapPin.sliceW (R := 2) (h := 0))
  have hne : OrbifoldGapPin.centerNode ≠ OrbifoldGapPin.rimANode := by
    decide
  have hW : ∀ j : OrbifoldGapPin.Slice 2 0,
      j ≠ OrbifoldGapPin.centerNode →
      OrbifoldGapPin.sliceW OrbifoldGapPin.centerNode j = 1 := by
    intro j hj
    have hmem : j.1 ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
        (-1, 1, 0), (1, 0, -1), (0, -1, 1)} : Finset (ℤ × ℤ × ℤ)) := by
      have h2 := j.2
      simp only [OrbifoldGapPin.layerFinset_two_zero] at h2
      exact h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h
    · exact absurd (Subtype.ext h) hj
    all_goals
      norm_num [OrbifoldGapPin.sliceW, OrbifoldGapPin.centerNode, h]
  obtain ⟨F, hF0, hF1, hFE⟩ := fiedler_attained OrbifoldGapPin.sliceW
    OrbifoldGapPin.sliceW_symm OrbifoldGapPin.sliceW_nonneg hne
  have hnn : (0:ℝ) ≤ fiedler (OrbifoldGapPin.sliceW (R := 2) (h := 0)) :=
    fiedler_nonneg _ OrbifoldGapPin.sliceW_symm OrbifoldGapPin.sliceW_nonneg
  refine hnn.lt_of_ne' ?_
  intro hf0
  have hE0 : (∑ i, F i * laplacianOp OrbifoldGapPin.sliceW F i) = 0 := by
    have h := hFE
    rw [hf0] at h
    exact h
  have hconst : ∀ j, F j = F OrbifoldGapPin.centerNode := by
    intro j
    by_cases hj : j = OrbifoldGapPin.centerNode
    · rw [hj]
    · exact (eq_of_energy_eq_zero OrbifoldGapPin.sliceW
        OrbifoldGapPin.sliceW_symm OrbifoldGapPin.sliceW_nonneg F hE0
        (i := OrbifoldGapPin.centerNode) (j := j)
        (by rw [hW j hj]; exact one_ne_zero)).symm
  have hsum : (∑ i, F i) = 7 * F OrbifoldGapPin.centerNode := by
    calc (∑ i, F i) = ∑ _i : OrbifoldGapPin.Slice 2 0,
          F OrbifoldGapPin.centerNode :=
          Finset.sum_congr rfl (fun i _ => hconst i)
      _ = (Fintype.card (OrbifoldGapPin.Slice 2 0) : ℝ)
            * F OrbifoldGapPin.centerNode := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 7 * F OrbifoldGapPin.centerNode := by
          rw [OrbifoldGapPin.card_slice]; norm_num
  rw [hF0] at hsum
  have hFc : F OrbifoldGapPin.centerNode = 0 := by
    rcases mul_eq_zero.mp hsum.symm with h | h
    · norm_num at h
    · exact h
  have hFz : ∀ j, F j = 0 := fun j => (hconst j).trans hFc
  have hsq : (∑ i, F i ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hFz i]; norm_num
  rw [hsq] at hF1
  exact one_ne_zero hF1.symm

/-- **K-ALB-TRACK — FIRED as ANTI-TRACKING (Brick 2).** On
the pre-registered scaling family the seat's total thermal
albedo loss does NOT track its gap: at scale 2 the gap has
exactly doubled (`fiedler_smul`, the gap strictly positive)
while the sharp landscape's loss has strictly fallen
(`totalThermalAlbedoLoss_two_smul_sharp_lt`), at every β.
Gap up, loss down — the loss reads the landscape through
the index, whose leading `1` refuses to scale; the gap
reads the weight field, which scales outright. The verdict
is reported as found; the scope pre-registered the family
and did not prejudge the direction. (The finite gap is a
graph spectral quantity — it is not gravity; K-ALB-NAME.
Dial 2 stays 0.) -/
theorem albedoLoss_antitracks_gap_scaling (β : ℝ) :
    sliceFiedlerGap < fiedler (fun i j : OrbifoldGapPin.Slice 2 0 =>
      (2:ℝ) * OrbifoldGapPin.sliceW i j)
    ∧ totalThermalAlbedoLoss (fun i j => (2:ℝ) * OrbifoldGapPin.sliceW i j)
        sharpLandscape β
      < totalThermalAlbedoLoss OrbifoldGapPin.sliceW sharpLandscape β := by
  refine ⟨?_, totalThermalAlbedoLoss_two_smul_sharp_lt β⟩
  have hsmul := fiedler_smul OrbifoldGapPin.sliceW 2 (by norm_num)
  have hpos := sliceFiedlerGap_pos
  unfold sliceFiedlerGap at hpos ⊢
  rw [hsmul]
  linarith

/-- **The converse countermodel (Brick 2): the gap is not
determined by the loss.** There is no function of the total
thermal albedo loss that returns the Fiedler value along
the scaling family: the flat landscape's loss is exactly 1
at every scale (Brick 1 — total absorption at every weight
field), while the family's gap takes the value `0` at scale
0 and the slice's strictly positive gap at scale 1. Equal
loss, different gap. Together with Brick 1's
`albedoLoss_not_determined_by_gap`, the determination fails
in both directions. -/
theorem gap_not_determined_by_loss :
    ¬ ∃ f : ℝ → ℝ, ∀ (c : ℝ) (β : ℝ),
      fiedler (fun i j : OrbifoldGapPin.Slice 2 0 =>
        c * OrbifoldGapPin.sliceW i j)
        = f (totalThermalAlbedoLoss
            (fun i j => c * OrbifoldGapPin.sliceW i j) (fun _ => 0) β) := by
  rintro ⟨f, hf⟩
  have h0 := hf 0 1
  have h1 := hf 1 1
  rw [totalThermalAlbedoLoss_of_forall_eq _ _ _ (fun i j => rfl)] at h0 h1
  rw [fiedler_smul _ 0 (le_refl 0), zero_mul] at h0
  rw [fiedler_smul _ 1 zero_le_one, one_mul] at h1
  have hpos : (0:ℝ) < fiedler OrbifoldGapPin.sliceW := sliceFiedlerGap_pos
  rw [h1] at hpos
  rw [← h0] at hpos
  exact lt_irrefl 0 hpos

/-- **The surviving partial (Brick 2) — the independence of
the pair (gap, loss) over the seat family, in its labeled
form.** Three clauses, each an exhibition: (i) at FIXED
weights the loss varies with the landscape — exactly 1 on
the flat landscape, strictly less on the sharp one, at
every β (Brick 1); (ii) on the scaling family the gap
strictly rises while the sharp landscape's loss strictly
falls — anti-tracking (`albedoLoss_antitracks_gap_scaling`);
(iii) at FIXED (flat) loss the gap varies with the scale —
the loss is 1 at both scales while the gaps differ. The
gap reads the weight field and the loss reads the
landscape; over this seat family the two quantities vary
independently, and neither determines the other in either
direction. This is the pin's positive theorem — the honest
finite residue of the seeing. NO CLAIM; Dial 2 stays 0. -/
theorem albedo_gap_independence :
    (∀ β : ℝ, totalThermalAlbedoLoss OrbifoldGapPin.sliceW (fun _ => 0) β = 1
      ∧ totalThermalAlbedoLoss OrbifoldGapPin.sliceW sharpLandscape β < 1)
    ∧ (∀ β : ℝ, sliceFiedlerGap
        < fiedler (fun i j : OrbifoldGapPin.Slice 2 0 =>
          (2:ℝ) * OrbifoldGapPin.sliceW i j)
      ∧ totalThermalAlbedoLoss (fun i j => (2:ℝ) * OrbifoldGapPin.sliceW i j)
          sharpLandscape β
        < totalThermalAlbedoLoss OrbifoldGapPin.sliceW sharpLandscape β)
    ∧ (∀ β : ℝ, totalThermalAlbedoLoss
          (fun i j => (2:ℝ) * OrbifoldGapPin.sliceW i j) (fun _ => 0) β
        = totalThermalAlbedoLoss OrbifoldGapPin.sliceW (fun _ => 0) β
      ∧ sliceFiedlerGap
        ≠ fiedler (fun i j : OrbifoldGapPin.Slice 2 0 =>
          (2:ℝ) * OrbifoldGapPin.sliceW i j)) := by
  refine ⟨fun β => ⟨?_, ?_⟩, fun β => albedoLoss_antitracks_gap_scaling β,
    fun β => ⟨?_, ?_⟩⟩
  · exact totalThermalAlbedoLoss_of_forall_eq _ _ _ (fun i j => rfl)
  · exact totalThermalAlbedoLoss_sharp_lt_one β
  · rw [totalThermalAlbedoLoss_of_forall_eq _ _ _ (fun i j => rfl),
      totalThermalAlbedoLoss_of_forall_eq _ _ _ (fun i j => rfl)]
  · exact ne_of_lt (albedoLoss_antitracks_gap_scaling β).1

end ThetLogos
