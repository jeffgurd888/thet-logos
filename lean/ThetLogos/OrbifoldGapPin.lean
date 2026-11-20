/-
# OrbifoldGapPin — the slice–orbifold–gap move at the gravity orb (Seat 1)

**Scope: ~/workspace/your_files/slice-orbifold-gap-scope-2026-11-17.md,
Seat 1. Commissioned by Zero, 2026-11-17 00:40 EST ("do the same
thing as before with the slice and the orbifolding mapping to the
gap"); seat selection "All" (00:42 EST). NO CLAIM. Dials 0/4.
Dial-ineligible.**

WORKING LABEL: the module name `OrbifoldGapPin` is a working label
only — final naming is Zero's. The seat is Zero's image of
2026-11-17 00:38 EST: gravity as a sphere with a lattice woven
inside it.

THE SEAT: the ball `B_R = {p : ℤ³ | p₁² + p₂² + p₃² ≤ R²}` as a
finite type; the fold is Zero's triadic ℤ₃ twist of record
(chosen 2026-10-18) realized as the cyclic coordinate permutation
`cyc (x, y, z) = (z, x, y)` — rotation by 2π/3 about the (1,1,1)
body diagonal; the slice is the equatorial diagonal layer
`L₀ = {p ∈ B_R | x + y + z = 0}` with its nearest-neighbour graph
(weights of `BridgeLaplacian.laplacianOp`); the gap machine is the
in-tree Bridge Fiedler package (`BridgeLaplacian.fiedler`,
`BridgeCompletion`). Headline radius R = 2 (K-ORB-TRIVIAL, resolved
at scoping: at R = 1 the equatorial layer is the centre alone, so
R = 2 is the minimal honest radius; the slice there has 7 nodes —
a hexagon with a centre — in ℤ₃-orbits of sizes 1 + 3 + 3).

FINITE GAP ONLY: every gap in this module is a finite graph
spectral gap (a Fiedler value of a finite weighted graph, or an
eigenvalue of the finite quotient operator). It is NOT the
Yang–Mills / Clay gap, not a continuum gap, and no measured number
is derived. Parts of official statements closed: 0.

DISCLOSURE — THE QUOTIENT WEIGHTING (read before the theorems):
the quotient graph carries the REGULAR-QUOTIENT (per-node averaged)
weights `quotW o o' = (Σ_{p ∈ o} Σ_{q ∈ o'} sliceW p q) / |o|`.
This is the unique weighting for which pullback intertwines the
Laplacians (B3), and with it the quotient operator's spectrum is
exactly the cyc-invariant sector of the slice spectrum. The
inter-orbit TOTALS weighting also exists and is symmetric, but its
eigenvectors do not pull back to slice eigenvectors — it does not
intertwine, so it is not used. The averaged weighting is NOT
symmetric in the plain counting inner product when orbit sizes
differ (at R = 2: `quotW centre rim = 3` against
`quotW rim centre = 1`), so `BridgeCompletion`'s variational
`fiedler` — which is stated for symmetric weights — does not apply
to the quotient side directly. The gap comparison is therefore
carried in eigenpair form (B4): every eigenvalue of the quotient
operator carried by a nonconstant eigenvector bounds the slice's
Fiedler value from above — folding can only raise the gap — and
equality holds iff an invariant Fiedler eigenvector exists on the
slice. (Numeric scoping check, not Lean content: slice spectrum
{0, 2, 2, 4, 4, 5, 7}, invariant sector {0, 5, 7} = the averaged
quotient's spectrum, totals quotient spectrum {0, 9, 15}.)
K-ORB-INTERTWINE does not fire: an intertwining weighting exists
and is the one used.
-/

import ThetLogos.BridgeCompletion

namespace ThetLogos
namespace OrbifoldGapPin

/-! ## Brick 1 — the ball and the triadic action -/

/-- The squared norm on ℤ³. -/
def normSq (p : ℤ × ℤ × ℤ) : ℤ := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

/-- The cyclic coordinate permutation `cyc (x, y, z) = (z, x, y)`:
rotation by 2π/3 about the (1,1,1) diagonal. -/
def cyc (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (p.2.2, p.1, p.2.1)

/-- The ball of radius `R` in ℤ³, as a finset: lattice points in
the cube `[-R, R]³` with `normSq ≤ R²`. -/
def ballFinset (R : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-(R : ℤ)) (R : ℤ)).product
    ((Finset.Icc (-(R : ℤ)) (R : ℤ)).product
      (Finset.Icc (-(R : ℤ)) (R : ℤ)))).filter (fun p => normSq p ≤ (R : ℤ) ^ 2)

/-- The ball as a finite type. -/
abbrev Ball (R : ℕ) : Type := ↥(ballFinset R)

/-- `cyc` preserves the squared norm (any coordinate permutation
does). -/
theorem cyc_normSq (p : ℤ × ℤ × ℤ) : normSq (cyc p) = normSq p := by
  obtain ⟨x, y, z⟩ := p
  show (z ^ 2 + x ^ 2 + y ^ 2 : ℤ) = x ^ 2 + y ^ 2 + z ^ 2
  ring

/-- `cyc` has order 3. -/
theorem cyc_iter3 (p : ℤ × ℤ × ℤ) : cyc (cyc (cyc p)) = p := by
  obtain ⟨x, y, z⟩ := p
  rfl

/-- The ball is `cyc`-invariant. -/
theorem cyc_mem_ballFinset {R : ℕ} {p : ℤ × ℤ × ℤ}
    (hp : p ∈ ballFinset R) : cyc p ∈ ballFinset R := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hmem, hnorm⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx, hyz⟩ := Finset.mem_product.mp hmem
  obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨hz, Finset.mem_product.mpr ⟨hx, hy⟩⟩
  · rw [cyc_normSq]
    exact hnorm

/-- The fixed points of `cyc` are exactly the diagonal `x = y = z`. -/
theorem cyc_eq_self_iff (x y z : ℤ) :
    cyc (x, y, z) = (x, y, z) ↔ x = y ∧ y = z := by
  simp only [cyc, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(h1.trans h2).symm, h1, h2⟩

/-- The triadic action on the ball itself. -/
def cycBall (R : ℕ) (p : Ball R) : Ball R :=
  ⟨cyc p.1, cyc_mem_ballFinset p.2⟩

/-- The action on the ball has order 3. -/
theorem cycBall_iter3 (R : ℕ) (p : Ball R) :
    cycBall R (cycBall R (cycBall R p)) = p := by
  apply Subtype.ext
  show cyc (cyc (cyc p.1)) = p.1
  exact cyc_iter3 p.1

/-! ## Brick 2a — layers and the slice graph -/

/-- The diagonal coordinate sum. Layers are its level sets. -/
def coordSum (p : ℤ × ℤ × ℤ) : ℤ := p.1 + p.2.1 + p.2.2

/-- The diagonal layer `L_h = {p ∈ B_R | x + y + z = h}`, as a finset. -/
def layerFinset (R : ℕ) (h : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (ballFinset R).filter (fun p => coordSum p = h)

/-- A slice: the layer as a finite type. -/
abbrev Slice (R : ℕ) (h : ℤ) : Type := ↥(layerFinset R h)

/-- `cyc` preserves the coordinate sum. -/
theorem cyc_coordSum (p : ℤ × ℤ × ℤ) : coordSum (cyc p) = coordSum p := by
  obtain ⟨x, y, z⟩ := p
  show (z + x + y : ℤ) = x + y + z
  ring

/-- Every layer is `cyc`-invariant. -/
theorem cyc_mem_layerFinset {R : ℕ} {h : ℤ} {p : ℤ × ℤ × ℤ}
    (hp : p ∈ layerFinset R h) : cyc p ∈ layerFinset R h := by
  rw [layerFinset, Finset.mem_filter] at hp ⊢
  refine ⟨cyc_mem_ballFinset hp.1, ?_⟩
  rw [cyc_coordSum]
  exact hp.2

/-- The triadic action on a slice. -/
def cycSlice (R : ℕ) (h : ℤ) (p : Slice R h) : Slice R h :=
  ⟨cyc p.1, cyc_mem_layerFinset p.2⟩

/-- The action on a slice has order 3. -/
theorem cycSlice_iter3 (R : ℕ) (h : ℤ) (p : Slice R h) :
    cycSlice R h (cycSlice R h (cycSlice R h p)) = p := by
  apply Subtype.ext
  show cyc (cyc (cyc p.1)) = p.1
  exact cyc_iter3 p.1

/-- The slice graph's weights: `1` on nearest neighbours (squared
distance `2` — the permutations of `(1, -1, 0)`), else `0`. -/
def sliceW {R : ℕ} {h : ℤ} (p q : Slice R h) : ℝ :=
  if (p.1.1 - q.1.1) ^ 2 + (p.1.2.1 - q.1.2.1) ^ 2 + (p.1.2.2 - q.1.2.2) ^ 2 = 2
    then 1 else 0

/-- The slice weights are symmetric. -/
theorem sliceW_symm {R : ℕ} {h : ℤ} (p q : Slice R h) :
    sliceW p q = sliceW q p := by
  have hsq : (p.1.1 - q.1.1) ^ 2 + (p.1.2.1 - q.1.2.1) ^ 2
      + (p.1.2.2 - q.1.2.2) ^ 2
      = (q.1.1 - p.1.1) ^ 2 + (q.1.2.1 - p.1.2.1) ^ 2
      + (q.1.2.2 - p.1.2.2) ^ 2 := by ring
  unfold sliceW
  rw [hsq]

/-- The slice weights are `cyc`-invariant — the fold is a symmetry
of the slice graph. -/
theorem sliceW_cyc {R : ℕ} {h : ℤ} (p q : Slice R h) :
    sliceW (cycSlice R h p) (cycSlice R h q) = sliceW p q := by
  have hsq : ((cycSlice R h p).1.1 - (cycSlice R h q).1.1) ^ 2
      + ((cycSlice R h p).1.2.1 - (cycSlice R h q).1.2.1) ^ 2
      + ((cycSlice R h p).1.2.2 - (cycSlice R h q).1.2.2) ^ 2
      = (p.1.1 - q.1.1) ^ 2 + (p.1.2.1 - q.1.2.1) ^ 2
      + (p.1.2.2 - q.1.2.2) ^ 2 := by
    obtain ⟨⟨x, y, z⟩, -⟩ := p
    obtain ⟨⟨x', y', z'⟩, -⟩ := q
    show (z - z') ^ 2 + (x - x') ^ 2 + (y - y') ^ 2
      = (x - x') ^ 2 + (y - y') ^ 2 + (z - z') ^ 2
    ring
  unfold sliceW
  rw [hsq]

/-! ## Brick 2b — the headline slice census (R = 2, h = 0) -/

/-- The slice weights are nonnegative. -/
theorem sliceW_nonneg {R : ℕ} {h : ℤ} (p q : Slice R h) :
    0 ≤ sliceW p q := by
  unfold sliceW
  split_ifs <;> norm_num

/-- The centre node of the headline slice. -/
def centerNode : Slice 2 0 := ⟨(0, 0, 0), by decide⟩

/-- A rim node in the first ℤ₃-orbit. -/
def rimANode : Slice 2 0 := ⟨(1, -1, 0), by decide⟩

/-- A rim node in the second ℤ₃-orbit. -/
def rimBNode : Slice 2 0 := ⟨(-1, 1, 0), by decide⟩

/-- The headline slice has exactly 7 nodes (K-ORB-TRIVIAL's
minimal honest radius: at R = 1 this layer is the centre alone). -/
theorem slice_card : (layerFinset 2 0).card = 7 := by decide

/-- The headline slice's vertex type has 7 elements. -/
theorem card_slice : Fintype.card (Slice 2 0) = 7 := by
  rw [Fintype.card_coe]
  exact slice_card

/-- The ℤ₃-orbit of a slice node, as a finset. -/
def orbitFinset {R : ℕ} {h : ℤ} (p : Slice R h) : Finset (Slice R h) :=
  {p, cycSlice R h p, cycSlice R h (cycSlice R h p)}

/-- The centre is fixed by the fold: its orbit has size 1. -/
theorem orbit_card_center : (orbitFinset centerNode).card = 1 := by decide

/-- The first rim orbit has size 3. -/
theorem orbit_card_rimA : (orbitFinset rimANode).card = 3 := by decide

/-- The second rim orbit has size 3. -/
theorem orbit_card_rimB : (orbitFinset rimBNode).card = 3 := by decide

/-! ## Brick 3a — the orbit quotient -/

/-- The orbit relation of the triadic action: `q` is in the orbit
of `p`. -/
def orbitRel (R : ℕ) (h : ℤ) (p q : Slice R h) : Prop :=
  q = p ∨ q = cycSlice R h p ∨ q = cycSlice R h (cycSlice R h p)

theorem orbitRel_symm {R : ℕ} {h : ℤ} {p q : Slice R h}
    (hpq : orbitRel R h p q) : orbitRel R h q p := by
  unfold orbitRel at hpq
  rcases hpq with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (cycSlice_iter3 R h p).symm)
  · exact Or.inr (Or.inl (cycSlice_iter3 R h p).symm)

theorem orbitRel_trans {R : ℕ} {h : ℤ} {p q r : Slice R h}
    (hpq : orbitRel R h p q) (hqr : orbitRel R h q r) :
    orbitRel R h p r := by
  unfold orbitRel at hpq hqr
  rcases hpq with rfl | rfl | rfl
  · rcases hqr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rcases hqr with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · rw [cycSlice_iter3]
      exact Or.inl rfl
  · rcases hqr with rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · rw [cycSlice_iter3]
      exact Or.inl rfl
    · rw [show cycSlice R h (cycSlice R h (cycSlice R h (cycSlice R h p)))
        = cycSlice R h p from cycSlice_iter3 R h (cycSlice R h p)]
      exact Or.inr (Or.inl rfl)

theorem orbitRel_equivalence (R : ℕ) (h : ℤ) :
    Equivalence (orbitRel R h) :=
  ⟨fun _ => Or.inl rfl, @orbitRel_symm R h, @orbitRel_trans R h⟩

/-- The orbit setoid on a slice. -/
instance orbitSetoid (R : ℕ) (h : ℤ) : Setoid (Slice R h) :=
  ⟨orbitRel R h, orbitRel_equivalence R h⟩

/-- The quotient of a slice by the triadic fold: the orbifold's
vertex type. -/
abbrev SliceQuot (R : ℕ) (h : ℤ) : Type := Quotient (orbitSetoid R h)

noncomputable instance (R : ℕ) (h : ℤ) : DecidableEq (SliceQuot R h) :=
  Classical.decEq _

noncomputable instance (R : ℕ) (h : ℤ) : Fintype (SliceQuot R h) :=
  Fintype.ofFinite _

/-! ## Brick 3b — the quotient weights -/

/-- The fibre of a quotient vertex: its orbit, as a finset of
slice nodes. -/
noncomputable def fiber {R : ℕ} {h : ℤ} (o : SliceQuot R h) : Finset (Slice R h) :=
  Finset.univ.filter (fun p => Quotient.mk (orbitSetoid R h) p = o)

/-- The quotient weights: the regular-quotient (per-node averaged)
inter-orbit edge counts — the unique weighting for which pullback
intertwines the Laplacians (see the header disclosure). -/
noncomputable def quotW {R : ℕ} {h : ℤ} (o o' : SliceQuot R h) : ℝ :=
  (∑ p ∈ fiber o, ∑ q ∈ fiber o', sliceW p q) / ((fiber o).card : ℝ)

/-- Weight bookkeeping across an orbit: the per-node edge count
from a node into any fixed fibre is constant across the node's
orbit (the fold is a symmetry of the slice graph). -/
theorem fiber_sum_const {R : ℕ} {h : ℤ} {p p' : Slice R h}
    (hp : orbitRel R h p p') (o' : SliceQuot R h) :
    (∑ q ∈ fiber o', sliceW p q) = ∑ q ∈ fiber o', sliceW p' q := by
  have maps_cyc : ∀ q ∈ fiber o', cycSlice R h q ∈ fiber o' := by
    intro q hq
    rw [fiber, Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hq.2]
    exact (Quotient.eq.mpr
      (show q ≈ cycSlice R h q from Or.inr (Or.inl rfl))).symm
  have maps_cyc2 : ∀ q ∈ fiber o', cycSlice R h (cycSlice R h q) ∈ fiber o' :=
    fun q hq => maps_cyc _ (maps_cyc _ hq)
  unfold orbitRel at hp
  rcases hp with rfl | rfl | rfl
  · rfl
  · refine Finset.sum_bij' (fun q _ => cycSlice R h q)
      (fun q _ => cycSlice R h (cycSlice R h q)) maps_cyc maps_cyc2 ?_ ?_ ?_
    · intro q _
      exact cycSlice_iter3 R h q
    · intro q _
      exact cycSlice_iter3 R h q
    · intro q _
      exact (sliceW_cyc p q).symm
  · refine Finset.sum_bij' (fun q _ => cycSlice R h (cycSlice R h q))
      (fun q _ => cycSlice R h q) maps_cyc2 maps_cyc ?_ ?_ ?_
    · intro q _
      exact cycSlice_iter3 R h q
    · intro q _
      exact cycSlice_iter3 R h q
    · intro q _
      exact ((sliceW_cyc (cycSlice R h p) (cycSlice R h q)).trans
        (sliceW_cyc p q)).symm

/-- The per-node fibre sum at `p` is the quotient weight of its
own orbit: the averaged weight is the per-node count. -/
theorem fiber_sum_eq {R : ℕ} {h : ℤ} (p : Slice R h)
    (o' : SliceQuot R h) :
    (∑ q ∈ fiber o', sliceW p q) = quotW (Quotient.mk (orbitSetoid R h) p) o' := by
  have hmem : p ∈ fiber (Quotient.mk (orbitSetoid R h) p) := by
    simp [fiber]
  have hcard : ((fiber (Quotient.mk (orbitSetoid R h) p)).card : ℝ) ≠ 0 := by
    have hpos : 0 < (fiber (Quotient.mk (orbitSetoid R h) p)).card :=
      Finset.card_pos.mpr ⟨p, hmem⟩
    exact_mod_cast hpos.ne'
  have hconst : ∀ p' ∈ fiber (Quotient.mk (orbitSetoid R h) p),
      (∑ q ∈ fiber o', sliceW p' q) = ∑ q ∈ fiber o', sliceW p q := by
    intro p' hp'
    rw [fiber, Finset.mem_filter] at hp'
    have hrel : orbitRel R h p' p := Quotient.eq.mp hp'.2
    exact (fiber_sum_const (orbitRel_symm hrel) o').symm
  unfold quotW
  rw [eq_div_iff hcard, Finset.sum_congr rfl hconst, Finset.sum_const,
    nsmul_eq_mul, mul_comm]

/-! ## Brick 3c — pullback and the intertwining -/

/-- Pullback of a quotient function to the slice: the
cyc-invariant functions are exactly the pullbacks. -/
def pullback {R : ℕ} {h : ℤ} (G : SliceQuot R h → ℝ) :
    Slice R h → ℝ :=
  fun p => G (Quotient.mk (orbitSetoid R h) p)

/-- Pullbacks are cyc-invariant. -/
theorem pullback_invariant {R : ℕ} {h : ℤ} (G : SliceQuot R h → ℝ)
    (p : Slice R h) :
    pullback G (cycSlice R h p) = pullback G p := by
  have hmk : Quotient.mk (orbitSetoid R h) (cycSlice R h p) = Quotient.mk (orbitSetoid R h) p :=
    (Quotient.eq.mpr
      (show p ≈ cycSlice R h p from Or.inr (Or.inl rfl))).symm
  unfold pullback
  rw [hmk]

/-- Descent of an invariant function to the quotient. -/
def descend {R : ℕ} {h : ℤ} (F : Slice R h → ℝ)
    (hF : ∀ p, F (cycSlice R h p) = F p) : SliceQuot R h → ℝ :=
  Quotient.lift F (fun a b hab => by
    have hab' : orbitRel R h a b := hab
    unfold orbitRel at hab'
    rcases hab' with rfl | rfl | rfl
    · rfl
    · exact (hF a).symm
    · exact ((hF (cycSlice R h a)).trans (hF a)).symm)

/-- Pullback after descent is the identity on invariant
functions. -/
theorem pullback_descend {R : ℕ} {h : ℤ} (F : Slice R h → ℝ)
    (hF : ∀ p, F (cycSlice R h p) = F p) :
    pullback (descend F hF) = F := by
  funext p
  rfl

/-- **Intertwining (the fold's headline).** Pullback commutes
with the Laplacians: `L_slice ∘ pullback = pullback ∘ L_quotient`.
Hence the quotient's spectrum is the cyc-invariant sector of the
slice's spectrum. -/
theorem intertwining {R : ℕ} {h : ℤ} (G : SliceQuot R h → ℝ)
    (p : Slice R h) :
    laplacianOp sliceW (pullback G) p
      = laplacianOp quotW G (Quotient.mk (orbitSetoid R h) p) := by
  have step1 : (∑ q : Slice R h, sliceW p q * (pullback G p - pullback G q))
      = ∑ o' : SliceQuot R h,
        ∑ q ∈ fiber o', sliceW p q * (pullback G p - pullback G q) :=
    (Finset.sum_fiberwise_of_maps_to
      (fun q _ => Finset.mem_univ (Quotient.mk (orbitSetoid R h) q))
      (fun q => sliceW p q * (pullback G p - pullback G q))).symm
  have step2 : ∀ o' : SliceQuot R h,
      (∑ q ∈ fiber o', sliceW p q * (pullback G p - pullback G q))
        = quotW (Quotient.mk (orbitSetoid R h) p) o' * (G (Quotient.mk (orbitSetoid R h) p) - G o') := by
    intro o'
    rw [← fiber_sum_eq p o', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [fiber, Finset.mem_filter] at hq
    have h2 : pullback G q = G o' := by
      unfold pullback
      rw [hq.2]
    rw [h2, show pullback G p = G (Quotient.mk (orbitSetoid R h) p) from rfl]
  rw [laplacianOp_apply, laplacianOp_apply, step1]
  exact Finset.sum_congr rfl (fun o' _ => step2 o')

/-! ## Brick 4 — the gap correspondence -/

/-- The mean of a slice function. -/
noncomputable def sliceMean {R : ℕ} {h : ℤ} (F : Slice R h → ℝ) : ℝ :=
  (∑ p, F p) / (Fintype.card (Slice R h) : ℝ)

/-- Centring a function makes it mean-zero. -/
theorem sum_sub_sliceMean {R : ℕ} {h : ℤ} (F : Slice R h → ℝ)
    (hcard : (Fintype.card (Slice R h) : ℝ) ≠ 0) :
    ∑ p, (F p - sliceMean F) = 0 := by
  have hmean : (Fintype.card (Slice R h) : ℝ) * sliceMean F
      = ∑ p, F p := by
    unfold sliceMean
    field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hmean, sub_self]

/-- Eigenvectors pull back: a quotient eigenvector is a slice
eigenvector (invariant by `pullback_invariant`), same eigenvalue. -/
theorem pullback_eigen {R : ℕ} {h : ℤ} {G : SliceQuot R h → ℝ} {μ : ℝ}
    (hG : ∀ o, laplacianOp quotW G o = μ * G o) (p : Slice R h) :
    laplacianOp sliceW (pullback G) p = μ * pullback G p :=
  (intertwining G p).trans (hG _)

/-- The centred pullback of a quotient eigenvector is a slice
eigenvector with the same eigenvalue: centring is free, because
`μ · (mean) = 0` — the total current of an eigenvector vanishes. -/
theorem laplacianOp_shifted_pullback {R : ℕ} {h : ℤ}
    {G : SliceQuot R h → ℝ} {μ : ℝ}
    (hG : ∀ o, laplacianOp quotW G o = μ * G o)
    (hcard : (Fintype.card (Slice R h) : ℝ) ≠ 0) (p : Slice R h) :
    laplacianOp sliceW (fun q => pullback G q - sliceMean (pullback G)) p
      = μ * (pullback G p - sliceMean (pullback G)) := by
  have hμm : μ * sliceMean (pullback G) = 0 := by
    have hsum : μ * (∑ q, pullback G q) = 0 := by
      rw [Finset.mul_sum,
        ← sum_laplacianOp_eq_zero sliceW sliceW_symm (pullback G)]
      apply Finset.sum_congr rfl
      intro q _
      exact (pullback_eigen hG q).symm
    unfold sliceMean
    rw [← mul_div_assoc, hsum, zero_div]
  have hfun : (fun q => pullback G q - sliceMean (pullback G))
      = pullback G - (fun _ => sliceMean (pullback G)) := by
    funext q
    simp [Pi.sub_apply]
  rw [hfun, laplacianOp_sub]
  simp only [Pi.sub_apply, Pi.zero_apply, laplacianOp_const, sub_zero]
  rw [pullback_eigen hG p, mul_sub, hμm, sub_zero]

/-- The centred pullback of a nonconstant quotient function is
nonzero. -/
theorem shifted_pullback_ne_zero {R : ℕ} {h : ℤ}
    {G : SliceQuot R h → ℝ} (hGnc : ∃ o o', G o ≠ G o') :
    (fun q => pullback G q - sliceMean (pullback G)) ≠ 0 := by
  intro hF
  obtain ⟨o, o', hoo'⟩ := hGnc
  obtain ⟨p, hp⟩ := Quotient.exists_rep o
  obtain ⟨p', hp'⟩ := Quotient.exists_rep o'
  have e1 : pullback G p = sliceMean (pullback G) :=
    sub_eq_zero.mp (congrFun hF p)
  have e2 : pullback G p' = sliceMean (pullback G) :=
    sub_eq_zero.mp (congrFun hF p')
  have go : G o = sliceMean (pullback G) := by
    rw [← hp]
    exact e1
  have go' : G o' = sliceMean (pullback G) := by
    rw [← hp']
    exact e2
  exact hoo' (go.trans go'.symm)

/-- Eigenvectors descend: an invariant slice eigenvector is a
quotient eigenvector, same eigenvalue. -/
theorem descend_eigen {R : ℕ} {h : ℤ} {F : Slice R h → ℝ} {μ : ℝ}
    (hF : ∀ p, F (cycSlice R h p) = F p)
    (hFeig : ∀ p, laplacianOp sliceW F p = μ * F p)
    (o : SliceQuot R h) :
    laplacianOp quotW (descend F hF) o = μ * descend F hF o := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep o
  rw [← hp]
  have h1 := intertwining (descend F hF) p
  rw [pullback_descend F hF] at h1
  have h2 : descend F hF (Quotient.mk (orbitSetoid R h) p) = F p :=
    congrFun (pullback_descend F hF) p
  rw [← h1, hFeig p, h2]

/-- **The gap mapping.** Every eigenvalue of the quotient
operator carried by a nonconstant eigenvector bounds the slice's
Fiedler value from above: folding can only raise the gap. (The
quotient operator is not plain-symmetric — see the header — so
the comparison is carried in this eigenpair form rather than by
applying the variational `fiedler` to the quotient.) -/
theorem fiedler_slice_le_of_eigen_quotient {R : ℕ} {h : ℤ}
    {G : SliceQuot R h → ℝ} {μ : ℝ}
    (hG : ∀ o, laplacianOp quotW G o = μ * G o)
    (hGnc : ∃ o o', G o ≠ G o')
    (hcard : (Fintype.card (Slice R h) : ℝ) ≠ 0) :
    fiedler (sliceW (R := R) (h := h)) ≤ μ :=
  fiedler_le_of_eigenvector sliceW sliceW_symm sliceW_nonneg
    (fun q => pullback G q - sliceMean (pullback G)) μ
    (sum_sub_sliceMean (pullback G) hcard)
    (shifted_pullback_ne_zero hGnc)
    (fun p => laplacianOp_shifted_pullback hG hcard p)

/-- **The equality criterion** (stated, not decided): the
quotient operator carries the slice's own Fiedler value as an
eigenvalue of a nonconstant eigenvector iff the slice has an
invariant Fiedler eigenvector — equality in the gap mapping holds
exactly when the fold's gap is attained inside the slice. -/
theorem fiedler_eq_iff_invariant_eigen {R : ℕ} {h : ℤ}
    (hcard : (Fintype.card (Slice R h) : ℝ) ≠ 0) :
    (∃ G : SliceQuot R h → ℝ, (∃ o o', G o ≠ G o')
      ∧ ∀ o, laplacianOp quotW G o = fiedler (sliceW (R := R) (h := h)) * G o)
    ↔ ∃ F : Slice R h → ℝ, (∀ p, F (cycSlice R h p) = F p) ∧ F ≠ 0
      ∧ (∑ p, F p = 0)
      ∧ ∀ p, laplacianOp sliceW F p = fiedler (sliceW (R := R) (h := h)) * F p := by
  constructor
  · rintro ⟨G, hnc, heig⟩
    refine ⟨fun q => pullback G q - sliceMean (pullback G), ?_, ?_, ?_,
      fun p => laplacianOp_shifted_pullback heig hcard p⟩
    · intro p
      show pullback G (cycSlice R h p) - sliceMean (pullback G)
        = pullback G p - sliceMean (pullback G)
      rw [pullback_invariant]
    · exact shifted_pullback_ne_zero hnc
    · exact sum_sub_sliceMean (pullback G) hcard
  · rintro ⟨F, hinv, hne, hsum, heig⟩
    refine ⟨descend F hinv, ?_, fun o => descend_eigen hinv heig o⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp⟩ : ∃ p, F p ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hFconst : ∀ q, F q = F p := by
      intro q
      have e1 : F q = descend F hinv (Quotient.mk (orbitSetoid R h) q) :=
        (congrFun (pullback_descend F hinv) q).symm
      have e2 : F p = descend F hinv (Quotient.mk (orbitSetoid R h) p) :=
        (congrFun (pullback_descend F hinv) p).symm
      rw [e1, e2]
      exact hcon _ _
    have hsum2 : (∑ q, F q) = (Fintype.card (Slice R h) : ℝ) * F p := by
      rw [Finset.sum_congr rfl (fun q _ => hFconst q), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [hsum] at hsum2
    rcases (mul_eq_zero.mp hsum2.symm) with h | h
    · exact absurd h hcard
    · exact hp h

end OrbifoldGapPin
end ThetLogos
