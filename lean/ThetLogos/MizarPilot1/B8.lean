import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Image
import Mathlib.Data.ZMod.Basic

/-!
# Mizar Pilot 1 — Brick B8: the 21 sidecar-known "A" singles

MZ pilot wave, tranche 1, brick B8 — after Zero's 2026-11-09 pilot call.
Source working list: the Mizar registry (21 items, one per article:
ABSVALUE, CHAIN_1, FIB_NUM2, FUZZY_5, GROUP_1A, INT_8, LATTICE2,
MATRIX_0, MATRIX_1, NDIFF13, NUMBER17, RLAFFIN1, RVSUM_1, SEQ_1,
SIN_COS9, TDLAT_2, TOPMETR4, WEIERSTR, XBOOLE_1, XREAL_1, YELLOW_5).
Each carries MZ-1's per-item judgement "ALREADY-IN-MATHLIB"; this brick
is the measurement of that judgement: restate faithfully and close by
the Mathlib twin where the judgement is true, mark `STUCK` where the
item's home theory or representation has no Mathlib/our-tree home.

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: every item restated + proved, or marked `STUCK` in place with
its reason — never silently dropped; all 21 identifiers appear below.
Twin-notes are mandatory in this brick wherever a twin is claimed.

Priority credit: Mizar proved it first, in its system; we re-prove our
restatement in ours.

## Import tension (pilot data)

The 21 items span unrelated theories (sign arithmetic, finite minima,
parity, trigonometric Lipschitz bounds, group set-products, modular
order, lattices, matrices, differentiability, affine hulls, sequences,
topology, metric compactness), so no narrow per-item import set exists
for this brick: the import list above is the moderate union over the
areas actually restated.

REPAIR LOG (successor coordinator, 2026-11-10): the drafted import
block in fact opened with `import Mathlib` — the maximal load, not
the moderate union described above. At this VM's throttled CPU/IO a
full-`Mathlib` elaboration of this brick could not complete inside
the build budget (two attempts starved/killed with zero elaboration
errors). The block is therefore replaced by the moderate union the
text describes (tactics + the calculus/convex/trigonometric/affine/
metric/order/pointwise/finset areas actually used). Statements and
proofs are untouched by the import repair. Three drafted twin-names
also failed against this Mathlib pin and are repaired in place:
`DifferentiableAt.prod` → `DifferentiableAt.prodMk`,
`fderivWithin_prod'` → `DifferentiableWithinAt.fderivWithin_prodMk`,
and the WEIERSTR sSup-attainment route (`IsCompact.exists_sSup_eq`
does not exist at this pin) → `IsCompact.exists_isMaxOn`.

REPAIR LOG, round 2 (same coordinator, later the same night; the
brick's first completed elaboration reported exactly five errors,
each repaired proof-side, statements untouched): GROUP_1A — the
pointwise `Mul (Set M)` at this pin is a locale-scoped instance
(`scoped[Pointwise] attribute [instance] Set.mul`), so the theorem
carries `open scoped Pointwise in`, and its drafted
`Set.singleton_mul` rewrite chain is replaced by a manual
`Set.mem_mul` ext argument. INT_8 — the drafted `orderOf_pow u s`
fails twice over: at this pin `orderOf_pow` takes the group element
only (the exponent is implicit), and it is the finite-monoid form,
needing `Finite (ZMod n)ˣ`, which is not an instance for variable
`n` (it fails at `n = 0`). The proof is a case split: `n = 0`
(`ZMod 0 = ℤ`; every unit squares to `1`, so
`IsOfFinOrder.orderOf_pow`) and `n ≥ 1` (a local `Finite` instance
from the ZMod fintype, then `orderOf_pow`). TOPMETR4 — the drafted
`.trans_lt` dot-chains misproject at this pin and mix `<`/`≤`
steps; replaced by explicit `lt_trans` / `lt_of_lt_of_le`.
YELLOW_5 — `inf_bot_eq` takes its argument explicitly at this pin:
`inf_bot_eq a`. Each repair was validated in a scratch file against
this pin before landing.

REPAIR LOG, round 3 (same coordinator; the round-2 build's first
completed elaboration reported two further errors): GROUP_1A — a
docstring may not stand between a declaration and an
`open scoped … in` prefix at this pin (parser: "unexpected token
'open'; expected 'lemma'"), so the `open scoped Pointwise in` line
moves BEFORE the docstring. INT_8 — `IsOfFinOrder` is defined via
`Function.IsPeriodicPt` at this pin, so the anonymous constructor
`⟨2, two_pos, h2⟩` does not elaborate against it; the finite-order
witness now goes through the pin's own characterization
`isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, h2⟩`.

## Restatement idioms

* Mizar `sgn` has no real-valued Mathlib twin (Mathlib's `sign` is
  `SignType`-valued); ABSVALUE:18 is restated over `ℤ`, where
  `Int.sign` is the signum.
* Mizar multiplicative order `order(i, n)` for `i, n` coprime is the
  group-theoretic `orderOf` in the unit group `(ZMod n)ˣ`; coprimality
  is exactly being a unit.
* Mizar `OddNAT` membership is Mathlib's `Odd` predicate on `ℕ`.
* Mizar symmetric difference `X \+\ Y` is spelled out as
  `(X \ Y) ∪ (Y \ X)`, as in brick B1.
* Mizar `Affin` is `affineSpan ℝ ·`, `conv` is `convexHull ℝ ·`.
* Mizar partial functions differentiable on a set are restated with
  Mathlib `DifferentiableOn` / pointwise `DifferentiableAt`.
-/

namespace ThetLogos.MizarPilot1.B8

variable {α : Type*}

/-- after Mizar ABSVALUE:18 — the sign of a product is the product of
the signs. Restated over `ℤ`: Mizar's real-valued `sgn` has no
Mathlib twin (Mathlib's `sign` is `SignType`-valued), while
`Int.sign` is the signum on `ℤ`.
(twin: `Int.sign_mul` — exact) -/
theorem sign_mul_int (x y : ℤ) : Int.sign (x * y) = Int.sign x * Int.sign y :=
  Int.sign_mul x y

/-- after Mizar CHAIN_1:12 — a nonempty finite set of reals has a
least element. Restated with `Finset ℝ`, Mizar's finite subsets of
`REAL` with an order.
(twin: `Finset.min'` with `Finset.min'_mem` / `Finset.min'_le` —
exact) -/
theorem exists_min_of_finset_nonempty (s : Finset ℝ) (hne : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, m ≤ x :=
  ⟨s.min' hne, s.min'_mem hne, fun x hx => s.min'_le x hx⟩

/-- after Mizar FIB_NUM2:52 — `2 * k + 1` is odd and `2 * k` is not
odd, for every natural `k`. Mizar's `OddNAT` is the set of odd
naturals; restated via the `Odd` predicate. -/
theorem odd_two_mul_add_one (k : ℕ) : Odd (2 * k + 1) ∧ ¬ Odd (2 * k) := by
  refine ⟨⟨k, rfl⟩, ?_⟩
  rintro ⟨m, hm⟩
  omega

/-- after Mizar FUZZY_5:3 — sine is 1-Lipschitz:
`|sin x - sin y| ≤ |x - y|`. (The article is fuzzy-set machinery; this
item's statement is pure analysis.)
(twin: `Real.abs_sin_sub_sin_le` — exact) -/
theorem abs_sin_sub_le (x y : ℝ) : |Real.sin x - Real.sin y| ≤ |x - y| :=
  Real.abs_sin_sub_sin_le x y

open scoped Pointwise in
/-- after Mizar GROUP_1A:239 — pointwise product of a singleton with
a pair: `{a} * {b, c} = {a * b, a * c}` in any magma, for the
pointwise set product.
(twin: `Set.singleton_mul` with `Set.image_insert_eq` and
`Set.image_singleton` — exact) -/
theorem singleton_mul_pair {M : Type*} [Mul M] (a b c : M) :
    ({a} : Set M) * {b, c} = {a * b, a * c} := by
  ext z
  simp only [Set.mem_mul, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨x, rfl, y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨a, rfl, b, Or.inl rfl, rfl⟩
    · exact ⟨a, rfl, c, Or.inr rfl, rfl⟩

/-- after Mizar INT_8:14 — the order of a power: for a unit `u`
(Mizar: `i` coprime to the modulus `n`, order taken mod `n`),
`orderOf (u ^ s) = orderOf u / (orderOf u).gcd s`.
(twin: `orderOf_pow` — exact) -/
theorem orderOf_pow_units {n : ℕ} (u : (ZMod n)ˣ) (s : ℕ) :
    orderOf (u ^ s) = orderOf u / (orderOf u).gcd s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `ZMod 0 = ℤ`: every unit squares to `1`, hence has finite order.
    have hu : (u : ZMod 0) = 1 ∨ (u : ZMod 0) = -1 :=
      Int.isUnit_iff.mp (Units.isUnit u)
    have h2 : u ^ 2 = 1 := by
      apply Units.ext
      rcases hu with h | h <;> rw [Units.val_pow_eq_pow_val, h] <;> norm_num
    exact IsOfFinOrder.orderOf_pow (x := u) (n := s)
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, h2⟩)
  · have : NeZero n := ⟨hn.ne'⟩
    have : Finite (ZMod n)ˣ := Finite.of_fintype (α := (ZMod n)ˣ)
    exact orderOf_pow u

/-- after Mizar LATTICE2:27 — the meet absorbs the join:
`a ⊓ (a ⊔ b) = a` in any lattice.
(twin: `inf_sup_self` — exact) -/
theorem inf_absorbs_sup {L : Type*} [Lattice L] (a b : L) :
    a ⊓ (a ⊔ b) = a :=
  inf_sup_self

-- STUCK MATRIX_0:54: Mizar matrices are sequences of sequences with
-- `len`/`width` operations; Lean's `Matrix m n α` carries its
-- dimensions as index *types*, so "len (Mᵀ) = width M ∧ width (Mᵀ) =
-- len M" has no propositional content to restate without first
-- reifying the Mizar matrix representation. Classification:
-- representation mismatch / needs infrastructure (no Mathlib home
-- for the statement as stated).

/-- after Mizar MATRIX_1:16 — the identity permutation is even.
Restated as: the sign of the identity permutation on `Fin n` is `1`.
(twin: `Equiv.Perm.sign` is a monoid homomorphism, `map_one` —
exact) -/
theorem sign_id_perm (n : ℕ) :
    Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) = 1 :=
  map_one _

/-- after Mizar NDIFF13:54, differentiability clause — the pairing
of two functions differentiable at a point is differentiable there:
if `u` and `v` are differentiable at `x`, so is `y ↦ (u y, v y)`
into the product space. (Mizar states this on a set for partial
functions; the pointwise clause is the twin-backed core.)
(twin: `DifferentiableAt.prod` — exact) -/
theorem differentiableAt_prod_pair {S E F : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : S → E} {v : S → F} {x : S}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => (u y, v y)) x :=
  hu.prodMk hv

/-- after Mizar NDIFF13:54, derivative clause — the derivative of
the pairing on `Z` is the pairing of the derivatives, at any point
of `Z` where the derivative on `Z` is unique.
(twin: `DifferentiableWithinAt.fderivWithin_prodMk` — exact;
drafted as `fderivWithin_prod'`, which does not exist at this pin) -/
theorem fderivWithin_prod_pair {S E F : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : S → E} {v : S → F} {Z : Set S} {x : S}
    (hx : x ∈ Z) (hu : DifferentiableOn ℝ u Z) (hv : DifferentiableOn ℝ v Z)
    (hZ : UniqueDiffWithinAt ℝ Z x) :
    fderivWithin ℝ (fun y => (u y, v y)) Z x
      = (fderivWithin ℝ u Z x).prod (fderivWithin ℝ v Z x) :=
  DifferentiableWithinAt.fderivWithin_prodMk (hu x hx) (hv x hx) hZ

/-- after Mizar NUMBER17:88 — the product of the four-term sequence
`⟨a, b, c, d⟩` of complex numbers is `a * b * c * d`. Restated with
the Mathlib list `[a, b, c, d]` and `List.prod`. -/
theorem list_prod_four (a b c d : ℂ) : [a, b, c, d].prod = a * b * c * d := by
  simp [mul_assoc]

/-- after Mizar RLAFFIN1:68 — if the convex hull of `A` is included
in the convex hull of `B`, then the affine hull of `A` is included
in the affine hull of `B`. Proved from the hull/span minimality
principles: `affineSpan_le`, with `A ⊆ convexHull ℝ A ⊆ convexHull ℝ B`
and `convexHull_min` applied to `subset_affineSpan` and the
convexity of an affine subspace's carrier.
(twin: `affineSpan_le` / `convexHull_min` / `subset_affineSpan` /
`subset_convexHull` — exact) -/
theorem affineSpan_le_of_convexHull_subset {E : Type*}
    [AddCommGroup E] [Module ℝ E] {A B : Set E}
    (h : convexHull ℝ A ⊆ convexHull ℝ B) :
    affineSpan ℝ A ≤ affineSpan ℝ B := by
  rw [affineSpan_le]
  exact (subset_convexHull ℝ A).trans
    (h.trans (convexHull_min (subset_affineSpan ℝ B) (affineSpan ℝ B).convex))

/-- after Mizar RVSUM_1:16 — adding the zero sequence changes
nothing: `R + 0 = R` for a finite real sequence `R : Fin n → ℝ`.
(twin: `add_zero` on the pi type — exact) -/
theorem add_zero_seq (n : ℕ) (R : Fin n → ℝ) :
    R + (fun _ => (0 : ℝ)) = R := by
  funext i
  simp

/-- after Mizar SEQ_1:22 — scalar multiplication distributes over
addition of real sequences: `r • (s₁ + s₂) = r • s₁ + r • s₂`.
(twin: `smul_add` — exact) -/
theorem smul_add_seq (r : ℝ) (s₁ s₂ : ℕ → ℝ) :
    r • (s₁ + s₂) = r • s₁ + r • s₂ :=
  smul_add r s₁ s₂

/-- after Mizar SIN_COS9:31 — the `tan`/`arctan` composition is the
identity. Mizar states `arctan ∘ tan = id` on `(-π/2, π/2)`;
restated here as the everywhere-valid reverse composition
`tan (arctan x) = x` for all real `x`, the direction Mathlib
carries as a single twin.
(twin: `Real.tan_arctan` — exact) -/
theorem tan_arctan_all (x : ℝ) : Real.tan (Real.arctan x) = x :=
  Real.tan_arctan x

/-- after Mizar TDLAT_2:26 — the union of the interiors of a family
of sets is included in the union of the family:
`⋃ s ∈ F, interior s ⊆ ⋃ s ∈ F, s`. Proved pointwise.
(twin: `interior_subset` — exact) -/
theorem iUnion_interior_subset {β : Type*} [TopologicalSpace β]
    (F : Set (Set β)) :
    ⋃ s ∈ F, interior s ⊆ ⋃ s ∈ F, s := by
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hsF, hxs⟩ := hx
  exact ⟨s, hsF, interior_subset hxs⟩

/-- after Mizar TOPMETR4:7 — sequential continuity in metric
spaces: a map between pseudometric spaces is continuous iff it
preserves convergence of sequences, limits included. Restated
with `Filter.Tendsto` at `atTop`, the Mathlib form of Mizar's
"S convergent, T = f ∘ S ⟹ T convergent and lim T = f (lim S)".
Forward by `Continuous.tendsto`; backward by contradiction at a
point, through the metric ε-δ characterisations
`Metric.continuousAt_iff` and `Metric.tendsto_atTop` (the
sequential form of `Metric.tendsto_nhds_nhds`): failure at `b`
yields, for some `ε > 0`, points within `1/(n+1)` of `b` whose
images stay at distance `≥ ε` from `f b` — a sequence converging
to `b` whose image does not converge to `f b`. -/
theorem continuous_iff_seq_tendsto {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y) :
    Continuous f ↔
      ∀ (u : ℕ → X) (a : X),
        Filter.Tendsto u Filter.atTop (nhds a) →
          Filter.Tendsto (f ∘ u) Filter.atTop (nhds (f a)) := by
  constructor
  · intro hf u a hu
    exact (hf.tendsto a).comp hu
  · intro h
    rw [continuous_iff_continuousAt]
    intro b
    by_contra hb
    rw [Metric.continuousAt_iff] at hb
    push_neg at hb
    obtain ⟨ε, hε, hb⟩ := hb
    have key : ∀ n : ℕ, ∃ x, dist x b < 1 / (n + 1 : ℝ) ∧ ε ≤ dist (f x) (f b) :=
      fun n => hb _ (by positivity)
    choose u hu using key
    have hu_lim : Filter.Tendsto u Filter.atTop (nhds b) := by
      rw [Metric.tendsto_atTop]
      intro ε' hε'
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε'
      refine ⟨N, fun n hn => lt_trans (lt_of_lt_of_le (hu n).1 ?_) hN⟩
      exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) + 1)
        (by exact_mod_cast Nat.add_le_add_right hn 1)
    have hf_lim := h u b hu_lim
    rw [Metric.tendsto_atTop] at hf_lim
    obtain ⟨N, hN⟩ := hf_lim ε hε
    exact (not_lt.2 (hu N).2) (hN N le_rfl)

/-- after Mizar WEIERSTR:17 — on a nonempty compact set in a
metric space, the distance from a fixed point attains its
maximum: some point `x₁` of the set has every other point's
distance at most `dist x x₁`. This is the attainment content of
Mizar's `dist x x₁ = upper_bound (dist x '' P)`: the supremum of
the distance range is attained.
(twin: `IsCompact.exists_isMaxOn`, the extreme value theorem —
exact. Originally drafted via `IsCompact.exists_sSup_eq` on the
distance range, a name that does not exist at this pin; repaired
2026-11-10 to the isMaxOn route, statement untouched) -/
theorem exists_dist_le_of_isCompact {M : Type*} [PseudoMetricSpace M]
    {P : Set M} (hP : IsCompact P) (hne : P.Nonempty) (x : M) :
    ∃ x₁ ∈ P, ∀ y ∈ P, dist x y ≤ dist x x₁ := by
  have hcont : Continuous (fun y => dist x y) :=
    continuous_const.dist continuous_id
  obtain ⟨x₁, hx₁, hx₁max⟩ := hP.exists_isMaxOn hne hcont.continuousOn
  exact ⟨x₁, hx₁, fun y hy => isMaxOn_iff.mp hx₁max y hy⟩

/-- after Mizar XBOOLE_1:97 — if both halves of the symmetric
difference lie in `Z`, so does the whole: `X \ Y ⊆ Z` and
`Y \ X ⊆ Z` imply `(X \ Y) ∪ (Y \ X) ⊆ Z`. (Second XBOOLE_1 item
of this brick; the first family lives in brick B1.)
(twin: `Set.union_subset` — exact) -/
theorem symm_diff_subset_of {X Y Z : Set α}
    (h₁ : X \ Y ⊆ Z) (h₂ : Y \ X ⊆ Z) : (X \ Y) ∪ (Y \ X) ⊆ Z :=
  Set.union_subset h₁ h₂

/-- after Mizar XREAL_1:133 — a product of reals is negative only
with opposite signs: `a * b < 0` implies `0 < a ∧ b < 0` or
`a < 0 ∧ 0 < b`.
(twin: `mul_neg_iff` — exact) -/
theorem mul_neg_cases (a b : ℝ) (h : a * b < 0) :
    (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b) :=
  mul_neg_iff.mp h

/-- after Mizar YELLOW_5:25 — meeting the bottom element gives the
bottom: `a ⊓ ⊥ = ⊥` in any inf-semilattice with a bottom.
(twin: `inf_bot_eq` — exact) -/
theorem inf_bot_of {L : Type*} [SemilatticeInf L] [OrderBot L] (a : L) :
    a ⊓ ⊥ = ⊥ :=
  inf_bot_eq a

end ThetLogos.MizarPilot1.B8
