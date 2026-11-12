import Mathlib.Tactic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.WellFounded
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Mizar Pilot 2 — Brick B8: the 21 sidecar-known "A" singles (tranche 2)

MZ-W1-P2. MZ pilot wave, tranche 2, brick B8 — after Zero's 2026-11-09
pilot call, second draw.
Source working list: the Mizar registry (21 items, one per article:
CARD_1, COMPLEX1, FUNCT_4, GROUP_1, INTEGR21, JORDAN, LOPBAN_6,
MATRIX_1, NCFCONT2, NEWTON, PROB_2, RUSUB_1, RVSUM_1, SEQ_4, SURREAL1,
TOPALG_7, VECTSP_5, XBOOLEAN, XBOOLE_1, XXREAL_1, ZMODLAT1).
Each carries the draw tag "A" (the A/A? singles draw); this brick is
the measurement of MZ-1's ALREADY-IN-MATHLIB judgement for this draw,
at draft level, exactly as tranche 1's brick B8 measured its draw:
restate faithfully and close by the Mathlib twin where the judgement
is true, draft fresh where no single twin exists, and mark `STUCK`
where the item's home theory or representation has no Mathlib/our-tree
home. (Result for this draw: no item is stuck; see the brick report.)

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: every item restated + proved, or marked `STUCK` in place with
its reason — never silently dropped; all 21 identifiers appear below.
Twin-notes are mandatory in this brick wherever a twin is claimed.

Priority credit: Mizar proved it first, in its system; we re-prove our
restatement in ours.

## Import tension (pilot data)

The 21 items span unrelated theories (cardinals, complex numbers,
function overrides, groups, interval integrals, metric frontiers,
normed balls, matrices, uniform continuity, binomial coefficients,
set intersections, cosets, sequences and their shifts, well-orderings,
pointwise function products, linear projections, propositional
connectives, interval order), so no narrow per-item import set exists
for this brick: this file carries full `import Mathlib`. Full narrowing
is impossible here — that fact is itself pilot data about
scattered-single bricks (same tension as tranche 1's B8, recorded and
accepted for this brick shape).

## Restatement idioms

* Mizar equipotence `X,Y are_equipotent` is Mathlib's `Nonempty (X ≃ Y)`;
  `card X = card Y` is `Cardinal.mk X = Cardinal.mk Y`.
* Mizar postfix `"` on a group element is inversion; the registry line
  for GROUP_1:5 is transcribed in the draw as `g = h"` and is read here
  as `g = h⁻¹` (read literally as `g = h` the line would be false:
  `g = 2, h = 1/2` in `ℝ∖{0}` satisfies both product hypotheses).
* Mizar function override `f +* (a .--> b)` is `Function.update f a b`.
* Mizar `integral(f,c,d)` over `['c,d']` is the interval integral
  `∫ x in c..d, f x`; Mizar's continuity hypothesis is stronger than
  the twin needs (the interval-integral identity needs no hypothesis).
* Mizar `Fr Ball(x,r)` is `frontier (Metric.ball x r)`; `Sphere(x,r)`
  is `Metric.sphere x r`.
* Mizar `(-1) * Ball(0.X,r)` is the pointwise scalar action
  `(-1 : ℝ) • Metric.ball 0 r` on sets.
* Mizar coset membership `u, v ∈ C` for a coset `C` of `W` is restated
  in its difference form `u - v ∈ W` (same coset iff difference in `W`).
* Mizar shifted sequence `seq^\k` is `fun n => seq (n + k)`; Mizar
  `lim` is `Filter.Tendsto · Filter.atTop (nhds ·)`.
* Mizar `X is well-ordering` (a subset of a RelStr) is restated as
  `IsWellOrder ↥X (r.onFun Subtype.val)`: a well-ordering restricts
  to any subset.
* Mizar `v |-- (W,L)` is the pair of projections of `v` along the
  complementary pair `(W, L)`; restated via `Submodule.projection`.
* Mizar Z-lattice inner product `<; v, w ;>` is Mathlib's `⟪v, w⟫_ℝ`.
-/

namespace ThetLogos.MizarPilot2.B8

/-- after Mizar CARD_1:5 — two types are equipotent iff their
cardinals are equal: `X, Y are_equipotent ↔ card X = card Y`.
(twin: `Cardinal.eq` — exact) -/
theorem equipotent_iff_card_eq (X Y : Type 0) :
    Nonempty (X ≃ Y) ↔ Cardinal.mk X = Cardinal.mk Y :=
  Cardinal.eq.symm

/-- after Mizar COMPLEX1:13 — a complex number is its real part plus
its imaginary part times `i`: `Re z + (Im z) * <i> = z`.
(twin: `Complex.re_add_im` — exact) -/
theorem re_add_im_complex (z : ℂ) : (z.re : ℂ) + z.im * Complex.I = z :=
  Complex.re_add_im z

/-- after Mizar FUNCT_4:89 — overriding a function twice, the second
override wins at its own point:
`(f +* (a .--> b) +* (m .--> n)).m = n`.
(twin: `Function.update_self` — exact) -/
theorem update_update_apply (α β : Type*) [DecidableEq α]
    (f : α → β) (a m : α) (b n : β) :
    Function.update (Function.update f a b) m n m = n := by
  simp [Function.update_self]

/-- after Mizar GROUP_1:5 — two-sided inverse is unique: if
`h * g = 1_G` and `g * h = 1_G` then `g = h⁻¹` (the registry line's
postfix `"` is Mizar inversion). The first hypothesis alone suffices.
(twin: `eq_inv_of_mul_eq_one_left` — exact) -/
theorem eq_inv_of_mul_eq_one {G : Type*} [Group G] {g h : G}
    (h1 : g * h = 1) (h2 : h * g = 1) : g = h⁻¹ :=
  eq_inv_of_mul_eq_one_left h1

/-- after Mizar INTEGR21:24 — the interval integral of the negative
is the negative of the interval integral:
`integral(-f,c,d) = -integral(f,c,d)`. Mizar assumes `f` continuous
on `['a,b']` with `c, d ∈ ['a,b']`; the twin needs no hypothesis.
(twin: `intervalIntegral.integral_neg` — exact) -/
theorem intervalIntegral_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (c d : ℝ) :
    ∫ x in c..d, -f x = -∫ x in c..d, f x :=
  intervalIntegral.integral_neg

/-- after Mizar JORDAN:24 — the frontier of a ball of nonzero radius
in a real seminormed space is its sphere: `Fr Ball(x,r) = Sphere(x,r)`.
(twin: `frontier_ball` — exact) -/
theorem frontier_ball_eq_sphere {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (Metric.ball x r) = Metric.sphere x r :=
  frontier_ball x hr

open scoped Pointwise in
/-- after Mizar LOPBAN_6:11 — the ball at the origin is symmetric:
`Ball(0.X,r) = (-1) * Ball(0.X,r)`. Proved by extensionality through
the smul-set membership characterisation and `‖-y‖ = ‖y‖`. -/
theorem neg_one_smul_ball_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) :
    (-1 : ℝ) • Metric.ball (0 : E) r = Metric.ball (0 : E) r := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (show (-1 : ℝ) ≠ 0 by norm_num)]
  simp only [inv_neg_one, neg_one_smul, Metric.mem_ball, dist_eq_norm,
    sub_zero, norm_neg]

/-- after Mizar MATRIX_1:3 — matrix addition commutes:
`A + B = B + A` for matrices over a ring.
(twin: `add_comm` on the `Matrix` additive group — exact) -/
theorem matrix_add_comm {m n : Type*} {F : Type*} [AddCommGroup F]
    (A B : Matrix m n F) : A + B = B + A :=
  add_comm A B

/-- after Mizar NCFCONT2:2 — uniform continuity on a set restricts to
any subset: `f is_uniformly_continuous_on X` and `X1 ⊆ X` imply
`f is_uniformly_continuous_on X1`. (Mizar: partial functions between
complex normed spaces; restated for total maps between uniform spaces.)
(twin: `UniformContinuousOn.mono` — exact) -/
theorem uniformContinuousOn_mono_restrict {X Y : Type*}
    [UniformSpace X] [UniformSpace Y] (f : X → Y) {S S₁ : Set X}
    (hf : UniformContinuousOn f S) (h : S₁ ⊆ S) :
    UniformContinuousOn f S₁ :=
  hf.mono h

/-- after Mizar NEWTON:20 — binomial symmetry in the registry's form:
`s ≥ t` and `r = s - t` imply `s choose t = s choose r`.
(twin: `Nat.choose_symm` — exact) -/
theorem choose_eq_choose_sub {s t : ℕ} (h : t ≤ s) (r : ℕ) (hr : r = s - t) :
    Nat.choose s t = Nat.choose s r := by
  rw [hr]
  exact (Nat.choose_symm h).symm

/-- after Mizar PROB_2:5 — intersection distributes into a countable
intersection: `(⋂ n, ASeq n) ∩ B = ⋂ n, (ASeq n ∩ B)`. The registry
premise (`BSeq.n = ASeq.n /\ B` for all `n`, defining `BSeq` from
`ASeq`) is the definition of the right-hand family; the assertion is
the distribution identity.
(twin: `Set.iInter_inter` — exact) -/
theorem iInter_inter_apply {α : Type*} (ASeq : ℕ → Set α) (B : Set α) :
    (⋂ n, ASeq n) ∩ B = ⋂ n, (ASeq n ∩ B) :=
  Set.iInter_inter B ASeq

/-- after Mizar RUSUB_1:73 — two vectors in one coset of `W` differ by
an element of `W`: if `u, v` lie in a coset `C` of `W` (restated in
difference form: `u - v ∈ W`), then some `v₁ ∈ W` has `u + v₁ = v`. -/
theorem exists_add_mem_submodule {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (W : Submodule ℝ V) (u v : V) (h : u - v ∈ W) :
    ∃ w ∈ W, u + w = v := by
  refine ⟨v - u, ?_, by rw [add_comm, sub_add_cancel]⟩
  rw [← neg_sub]
  exact W.neg_mem h

/-- after Mizar RVSUM_1:32 — subtracting the zero sequence changes
nothing: `R - (i ↦ 0) = R` for a real sequence `R`.
(twin: `sub_zero` on the pi type — exact) -/
theorem sub_zero_seq (R : ℕ → ℝ) : R - (fun _ => (0 : ℝ)) = R :=
  sub_zero R

/-- after Mizar SEQ_4:20 — shifting a convergent sequence does not
change its limit: `seq convergent → lim (seq^\k) = lim seq`.
(twin: `Filter.tendsto_add_atTop_iff_nat` — exact) -/
theorem tendsto_shift {E : Type*} [TopologicalSpace E]
    (s : ℕ → E) (L : E) (k : ℕ)
    (h : Filter.Tendsto s Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => s (n + k)) Filter.atTop (nhds L) :=
  (Filter.tendsto_add_atTop_iff_nat k).mpr h

/-- after Mizar SURREAL1:26 — a subset of a well-ordering is a
well-ordering: `X ⊆ Y` and `Y is well-ordering` imply `X is
well-ordering`. Restated as restriction from the ambient relation
(apply inside `↥Y` for the registry's two-subset form).
(twin: `Function.Injective.isWellOrder` at `Subtype.val` — exact) -/
theorem isWellOrder_subtype {α : Type*} {r : α → α → Prop}
    [IsWellOrder α r] (X : Set α) :
    IsWellOrder X (r.onFun Subtype.val) :=
  Subtype.val_injective.isWellOrder r

/-- after Mizar TOPALG_7:1 — pointwise multiplication of functions
into an associative magma is associative:
`f(#)g(#)h = f(#)(g(#)h)`. Proved pointwise. -/
theorem pointwise_mul_assoc {X T : Type*} [Semigroup T]
    (f g h : X → T) : (f * g) * h = f * (g * h) := by
  funext x
  simp only [Pi.mul_apply]
  exact mul_assoc _ _ _

/-- after Mizar VECTSP_5:53 — the two projections along a linear
complement decompose the vector: for `L` a linear complement of `W`,
`(v |-- (W,L))`1 + (v |-- (W,L))`2 = v`.
(twin: `Submodule.projection_add_projection_eq_self` — exact) -/
theorem proj_add_proj {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] {W L : Submodule K E} (h : IsCompl W L) (v : E) :
    (W.projection L h) v + (L.projection W h.symm) v = v :=
  Submodule.projection_add_projection_eq_self h v

/-- after Mizar XBOOLEAN:95 — the propositional identity
`p 'xor' (p => q) = p 'nand' q`, restated over `Prop` as
`Xor p (p → q) ↔ ¬ (p ∧ q)`. Proved by cases on the two disjuncts. -/
theorem xor_imp_iff_nand (p q : Prop) : Xor p (p → q) ↔ ¬ (p ∧ q) := by
  constructor
  · intro h
    obtain (⟨hp, hn⟩ | ⟨hn, hnp⟩) := h
    · exact fun hcon => hn (fun _ => hcon.2)
    · exact fun hcon => hnp hcon.1
  · intro h
    by_cases hp : p
    · exact Or.inl ⟨hp, fun himp => h ⟨hp, himp hp⟩⟩
    · exact Or.inr ⟨fun hp' => absurd hp' hp, hp⟩

/-- after Mizar XBOOLE_1:116 — intersection distributes over itself:
`X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z)`. Proved by extensionality. -/
theorem inter_inter_distrib {α : Type*} (X Y Z : Set α) :
    X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, hy, hz⟩
    exact ⟨⟨hx, hy⟩, hx, hz⟩
  · rintro ⟨⟨hx, hy⟩, -, hz⟩
    exact ⟨hx, hy, hz⟩

/-- after Mizar XXREAL_1:9 — a point of the half-open interval is
either interior or the right endpoint:
`x ∈ ].p,q.] → x ∈ ].p,q.[ ∨ x = q`. Proved from `Set.mem_Ioc`
by splitting `x ≤ q`. -/
theorem mem_Ioc_cases {p q x : ℝ} (h : x ∈ Set.Ioc p q) :
    x ∈ Set.Ioo p q ∨ x = q := by
  obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp h
  rcases h2.lt_or_eq with h | h
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr h

open scoped InnerProductSpace in
/-- after Mizar ZMODLAT1:12 — the inner product with zero vanishes on
both sides: `<; v, 0.L ;> = 0 ∧ <; 0.L, v ;> = 0`.
(twin: `inner_zero_right` / `inner_zero_left` — exact) -/
theorem inner_zero_both {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (v : V) :
    ⟪v, (0 : V)⟫_ℝ = 0 ∧ ⟪(0 : V), v⟫_ℝ = 0 :=
  ⟨inner_zero_right v, inner_zero_left v⟩

end ThetLogos.MizarPilot2.B8
