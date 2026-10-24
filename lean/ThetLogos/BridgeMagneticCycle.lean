import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import ThetLogos.BridgeMagneticFlux

/-!
# BridgeMagneticCycle — STEM bridge brick B4-GENERAL: flux-dependence via a spanning tree

*STEM = Spectral–Thermal ElectroMagnetic (Jeff's name, 2026-10-24).*

**NO CLAIM.** This module is brick **B4** of the STEM bridge scoped in
`whitepaper/stem-bridge-scoping-2026-10-24.md`. It proves the charter's
statement **S4** in full, relative to an explicitly carried spanning
tree: the gauge class of a connection `θ` is **determined by its
fundamental-cycle holonomies** — and, by bricks B2/B3/B4′, so are the
spectrum of `magLin w θ`, the heat trace `magHeatTrace w θ`, and every
face holonomy. B4′ (`BridgeMagneticFlux`) proved the face-restricted
form; this module is the general statement B4′ named as the bridge's
remainder. With it, the bridge's near bank (B1, B2, B3, B5) and both
flux bricks stand; nothing about any other charter is asserted here.

**The tree seat — read this before citing.** The corpus's connection
vocabulary (B1–B5) carries `θ` on *all ordered pairs* of vertices:
there is no edge set, and no `SimpleGraph` anywhere in the corpus (its
only mention is a doc contrast in `BridgeLaplacian`). The graph of
this brick is therefore the complete pair set, and a spanning tree of
it is carried as **explicit datum**: a root `r`, a parent function
`par`, and a depth function `depth` obeying `depth r = 0` and
`depth (par v) + 1 = depth v` for `v ≠ r` (so `par^[depth v] v = r`:
every vertex reaches the root in exactly `depth v` parent steps, §1).
This is the classical theorem's own shape — a tree is *chosen*, then
gauge fixing and determination are exact — and it is the only shape
available in this vocabulary: Mathlib does carry `SimpleGraph.IsTree`,
but it has **no cycle-space API**, and the corpus has no adjacency for
a `SimpleGraph` tree to span. Constructing the datum from a graph is
therefore not a gap in this brick's proofs; it is a statement this
vocabulary cannot make, recorded here rather than hidden. The value
`par r` is never used (every chain has exactly `depth`-many steps).

**What is proved.** §2: the tree-path holonomy `treeHol θ v` (the
product of `θ` along the parent chain from `v` to the root) and its
one-step recursion. §3: **global gauge fixing** — the normal form
`normalConn θ = gaugeConn (treeHol θ) θ` is gauge-equivalent to `θ`
and trivial on every tree edge (`normalConn θ v (par v) = 1`).
§4: telescoping (`treeHol` of a gauge transform differs from `treeHol`
by endpoint factors only), hence the fundamental-cycle holonomy
`cycleHol θ i j = treeHol θ i * θ i j * (treeHol θ j)⁻¹` — the product
of `θ` around the closed walk root→`i`, edge `j`→`i`, `j`→root — is
gauge-invariant, and the **determination theorem**, a full `↔`, not
an implication: `θ₂` is a gauge transform of `θ₁` iff
`cycleHol θ₁ = cycleHol θ₂` at every pair. §5: the normal form is the
*unique* tree-trivial representative of its class, and the readings
corollary in B4′'s package shape — equal cycle holonomies force equal
face holonomies, equal spectra, equal heat traces. Weld check
(A2): at `θ ≡ 1` every fundamental-cycle holonomy is `1`
(`cycleHol_one`).

**Fences (charter §5, on the face).** This is finite graph
bookkeeping: a U(1) connection on a finite pair set and operators on
a finite-dimensional space. It is **not** Maxwell theory (continuum
Maxwell has NO SEAT in this corpus), not a force-unification claim,
not a torsion claim, and not a modular-flux claim — the killed
EM-torsion paste, the killed "strong nuclear = electromagnetic"
identification, and the killed magnetophase flux
(`ModularFlux.magnetophaseFlux_vanishes`) stay killed. Parts of any
official Clay statement closed by this module: **0**.

- Status: brick B4-GENERAL — built 2026-10-24 under the STEM bridge
  charter; parent-verified 2026-10-24 (targeted build exit 0,
  strict recount, axiom check); verdict STANDS. Dossier:
  `whitepaper/stem-b4-cycle-determination-2026-10-24.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The tree datum and its depth arithmetic

The datum: a root `r`, a parent function `par`, a depth function
`depth`, with `depth r = 0` and the step law
`depth (par v) + 1 = depth v` off the root. Two consequences carry
the whole brick: depth drops by exactly one per parent step, and
iterating `par` exactly `depth v` times reaches the root. -/

/-- One parent step peels one iterate: `par^[m+1] v = par^[m] (par v)`,
by `iterate_add_apply`. The form every chain computation below uses. -/
theorem iterate_par_succ (par : V → V) (m : ℕ) (v : V) :
    par^[m + 1] v = par^[m] (par v) := by
  have h : par^[m] (par v) = par^[m] (par^[1] v) := by
    rw [Function.iterate_one]
  rw [h, ← Function.iterate_add_apply]

/-- Depth vanishes exactly at the root: off the root the step law
forces depth `≥ 1`. -/
theorem depth_eq_zero_iff (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v) {v : V} :
    depth v = 0 ↔ v = r := by
  constructor
  · intro h
    by_contra hv
    have h1 := hstep v hv
    omega
  · intro h
    rw [h, hdepth_r]

/-- Depth drops by exactly one per parent step, iterated: after `n`
parent steps (within the depth budget) the remaining depth is
`depth v - n`, stated as `depth (par^[n] v) + n = depth v`. -/
theorem depth_iterate_par (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v) :
    ∀ (n : ℕ) (v : V), n ≤ depth v → depth (par^[n] v) + n = depth v := by
  intro n
  induction n with
  | zero =>
    intro v _
    simp
  | succ n ih =>
    intro v hv
    have hvr : v ≠ r := by
      intro h
      rw [h, hdepth_r] at hv
      omega
    have h1 : depth (par v) + 1 = depth v := hstep v hvr
    have h2 : n ≤ depth (par v) := by omega
    have h3 := ih (par v) h2
    rw [iterate_par_succ]
    omega

/-- Every vertex reaches the root in exactly `depth v` parent steps:
the parent chains are finite paths to `r`, which is what makes the
parent datum a spanning tree of the complete pair set. -/
theorem iterate_par_eq_root (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v) (v : V) :
    par^[depth v] v = r := by
  have h := depth_iterate_par r par depth hdepth_r hstep (depth v) v le_rfl
  have h0 : depth (par^[depth v] v) = 0 := by omega
  exact (depth_eq_zero_iff r par depth hdepth_r hstep).mp h0

/-! ## §2. The tree-path holonomy

`treeHol θ v` is the product of `θ` along the parent chain
`v → par v → par² v → … → r`, one factor per step: the factor at step
`n` is `θ (par^[n+1] v) (par^[n] v)`, the phase of transport from
`par^[n] v` up to `par^[n+1] v` in B1's convention (`θ a b` is
transport from `b` to `a`). Read as a gauge function, it is the
classical tree gauge: walking from the root outward, it accumulates
exactly the phases the gauge fixing must cancel. -/

/-- **The tree-path holonomy**: the product of the connection along
the tree path from `v` up to the root. -/
noncomputable def treeHol (par : V → V) (depth : V → ℕ)
    (θ : V → V → Circle) (v : V) : Circle :=
  ∏ n ∈ Finset.range (depth v), θ (par^[n + 1] v) (par^[n] v)

/-- At the root the tree path is empty, so its holonomy is `1`. -/
theorem treeHol_root (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0) (θ : V → V → Circle) :
    treeHol par depth θ r = 1 := by
  simp [treeHol, hdepth_r]

/-- **One-step recursion**: the tree path from `v` is the first step
`v → par v` followed by the tree path from `par v`. This is the
induction the gauge fixing and the telescoping both run on. -/
theorem treeHol_step (r : V) (par : V → V) (depth : V → ℕ)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    {θ : V → V → Circle} {v : V} (hv : v ≠ r) :
    treeHol par depth θ v
      = θ (par v) v * treeHol par depth θ (par v) := by
  have hd : depth (par v) + 1 = depth v := hstep v hv
  unfold treeHol
  rw [← hd, Finset.prod_range_succ', mul_comm]
  congr 1

/-! ## §3. Global gauge fixing on the tree

The normal form of `θ` is its gauge transform by its own tree
holonomy. It is gauge-equivalent to `θ` by construction (it *is* a
gauge transform of `θ`), and the recursion of §2 plus the connection
antisymmetry make it trivial on every tree edge: at the edge
`(v, par v)` the first tree step's phase is exactly cancelled. -/

/-- **The normal form** of a connection: `θ` gauge-transformed by its
own tree holonomy. The candidate canonical representative of the
gauge class of `θ` — §5 proves it is the unique tree-trivial one. -/
noncomputable def normalConn (par : V → V) (depth : V → ℕ)
    (θ : V → V → Circle) : V → V → Circle :=
  gaugeConn (treeHol par depth θ) θ

theorem normalConn_apply (par : V → V) (depth : V → ℕ)
    (θ : V → V → Circle) (i j : V) :
    normalConn par depth θ i j
      = treeHol par depth θ i * θ i j * (treeHol par depth θ j)⁻¹ :=
  rfl

/-- **Global gauge fixing on the tree**: the normal form is trivial
on every tree edge. Together with `normalConn`'s definition (a gauge
transform of `θ`), this says every gauge class has a representative
vanishing on the tree — the gauge is fixed globally, in one step,
by the tree holonomy. -/
theorem normalConn_trivial_on_tree (r : V) (par : V → V) (depth : V → ℕ)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹)
    {v : V} (hv : v ≠ r) :
    normalConn par depth θ v (par v) = 1 := by
  have hθ' : θ v (par v) = (θ (par v) v)⁻¹ := by
    rw [hθ v (par v), inv_inv]
  rw [normalConn_apply, treeHol_step r par depth hstep hv, hθ']
  rw [show θ (par v) v * treeHol par depth θ (par v) * (θ (par v) v)⁻¹
        * (treeHol par depth θ (par v))⁻¹
      = (θ (par v) v * (θ (par v) v)⁻¹)
        * (treeHol par depth θ (par v) * (treeHol par depth θ (par v))⁻¹)
      from by ac_rfl]
  simp

/-- Gauge fixing, existential form: some gauge makes `θ` trivial on
every tree edge at once. -/
theorem exists_gauge_trivial_on_tree (r : V) (par : V → V)
    (depth : V → ℕ)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹) :
    ∃ g : V → Circle, ∀ v : V, v ≠ r → gaugeConn g θ v (par v) = 1 :=
  ⟨treeHol par depth θ, fun v hv =>
    normalConn_trivial_on_tree r par depth hstep θ hθ hv⟩

/-! ## §4. Telescoping, the fundamental-cycle holonomy, determination

Gauge-transforming `θ` changes each tree-step phase by endpoint
factors (`θ^h (par v) v = h (par v) * θ (par v) v * (h v)⁻¹`), and
along a whole tree path the interior factors telescope away: only
the root and endpoint factors survive. That is the entire content of
the determination theorem — the fundamental-cycle holonomy
`cycleHol θ i j`, the product of `θ` around the closed walk
`j →(tree) root →(tree) i` closed by the edge `j → i`, is built from
`treeHol` at `i` and `j` and the single edge value `θ i j`, so the
endpoint factors cancel in it. It is therefore gauge-invariant, and
in §4's headline it is a *complete* invariant: equality of all
fundamental-cycle holonomies is equality of gauge classes. -/

/-- Successive gauge transformations compose and invert through the
pointwise group structure on gauge functions: applying `g` and then
`g⁻¹` returns the connection. A restatement of B4′'s
`gaugeConn_comp` in the form the determination proof consumes. -/
theorem gaugeConn_inv_apply (g : V → Circle) (θ : V → V → Circle) :
    gaugeConn g⁻¹ (gaugeConn g θ) = θ := by
  rw [gaugeConn_comp, inv_mul_cancel, gaugeConn_one]

/-- A connection is its own normal form's inverse gauge transform:
the normal form determines the connection back, explicitly. -/
theorem eq_gaugeConn_inv_normalConn (par : V → V) (depth : V → ℕ)
    (θ : V → V → Circle) :
    θ = gaugeConn (treeHol par depth θ)⁻¹ (normalConn par depth θ) :=
  (gaugeConn_inv_apply (treeHol par depth θ) θ).symm

/-- **Telescoping**, auxiliary form (induction on depth): the tree
holonomy of a gauge transform is the tree holonomy itself, corrected
only at the two ends of the path — the root factor `h r` and the
endpoint factor `(h v)⁻¹`. -/
theorem treeHol_gauge_aux (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (h : V → Circle) (θ : V → V → Circle) :
    ∀ (k : ℕ) (v : V), depth v = k →
      treeHol par depth (gaugeConn h θ) v
        = h r * treeHol par depth θ v * (h v)⁻¹ := by
  intro k
  induction k with
  | zero =>
    intro v hvk
    have hvr : v = r := (depth_eq_zero_iff r par depth hdepth_r hstep).mp hvk
    have h1 : treeHol par depth (gaugeConn h θ) v = 1 := by
      rw [hvr]
      exact treeHol_root r par depth hdepth_r _
    have h2 : treeHol par depth θ v = 1 := by
      rw [hvr]
      exact treeHol_root r par depth hdepth_r _
    rw [h1, h2, hvr]
    simp
  | succ k ih =>
    intro v hvk
    have hvr : v ≠ r := by
      intro hve
      rw [hve, hdepth_r] at hvk
      omega
    have hd : depth (par v) = k := by
      have h1 := hstep v hvr
      omega
    rw [treeHol_step r par depth hstep hvr,
      treeHol_step r par depth hstep hvr, ih (par v) hd, gaugeConn_apply]
    rw [show (h (par v) * θ (par v) v * (h v)⁻¹)
          * (h r * treeHol par depth θ (par v) * (h (par v))⁻¹)
        = (h (par v) * (h (par v))⁻¹)
          * (h r * (θ (par v) v * treeHol par depth θ (par v)) * (h v)⁻¹)
        from by ac_rfl]
    simp

/-- **Telescoping**: the tree holonomy of a gauge transform differs
from the tree holonomy by endpoint factors only. -/
theorem treeHol_gauge (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (h : V → Circle) (θ : V → V → Circle) (v : V) :
    treeHol par depth (gaugeConn h θ) v
      = h r * treeHol par depth θ v * (h v)⁻¹ :=
  treeHol_gauge_aux r par depth hdepth_r hstep h θ (depth v) v rfl

/-- **The fundamental-cycle holonomy** of the pair `(i, j)`: the
product of `θ` around the closed walk that climbs the tree from `j`
to the root, descends to `i`, and closes along the edge `j → i` —
equivalently (by `normalConn_eq_cycleHol`) the normal form's value
at `(i, j)`. One such cycle per ordered pair: the fundamental cycles
of the complete pair set relative to the tree. -/
noncomputable def cycleHol (par : V → V) (depth : V → ℕ)
    (θ : V → V → Circle) (i j : V) : Circle :=
  treeHol par depth θ i * θ i j * (treeHol par depth θ j)⁻¹

/-- The normal form *is* the fundamental-cycle holonomy table: the
canonical representative of a gauge class reads off, at each pair,
exactly that pair's cycle holonomy. -/
theorem normalConn_eq_cycleHol (par : V → V) (depth : V → ℕ)
    (θ : V → V → Circle) (i j : V) :
    normalConn par depth θ i j = cycleHol par depth θ i j :=
  rfl

/-- A three-factor cancellation in `Circle`, by explicit swaps
(the `group`/`ac_rfl` word tactics are unreliable on this corpus's
`Circle` goals; every rewrite here has all arguments explicit). -/
theorem circle_cancel_end {x y z : Circle} :
    (x * y * z⁻¹) * z = x * y := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- A five-factor cancellation in `Circle`, by explicit swaps:
the outer factor `x` and its inverse at the far end cancel through
the middle. -/
theorem circle_cancel_mid {x y z w : Circle} :
    (x * y) * z * (w⁻¹ * x⁻¹) = y * z * w⁻¹ := by
  rw [mul_right_comm (x * y) z (w⁻¹ * x⁻¹),
    mul_right_comm x y (w⁻¹ * x⁻¹),
    ← mul_assoc x w⁻¹ x⁻¹,
    mul_right_comm x w⁻¹ x⁻¹,
    mul_inv_cancel, one_mul,
    mul_comm w⁻¹ y,
    mul_right_comm y w⁻¹ z]

/-- **Gauge invariance of the fundamental-cycle holonomies**: the
endpoint factors of the telescoping cancel in `cycleHol`. The
forward half of determination. Proved through the normal forms:
both normal forms are gauge transforms of `θ` whose gauge functions
agree at the level of values, by the telescoping (`treeHol_gauge`)
and two explicit cancellations. -/
theorem cycleHol_gauge (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (h : V → Circle) (θ : V → V → Circle) (i j : V) :
    cycleHol par depth (gaugeConn h θ) i j
      = cycleHol par depth θ i j := by
  have hT : ∀ v : V, treeHol par depth (gaugeConn h θ) v * h v
      = h r * treeHol par depth θ v := by
    intro v
    rw [treeHol_gauge r par depth hdepth_r hstep h θ v]
    exact circle_cancel_end
  rw [← normalConn_eq_cycleHol, ← normalConn_eq_cycleHol]
  show gaugeConn (treeHol par depth (gaugeConn h θ)) (gaugeConn h θ) i j
    = gaugeConn (treeHol par depth θ) θ i j
  rw [gaugeConn_comp, gaugeConn_apply, gaugeConn_apply]
  simp only [Pi.mul_apply]
  rw [hT i, hT j, mul_inv_rev]
  exact circle_cancel_mid

/-- **THE DETERMINATION THEOREM (S4, general form).** Relative to
the tree datum, two connections are gauge-equivalent if and only if
all their fundamental-cycle holonomies agree. The gauge class of a
connection — the bridge's gauge-invariant content — is exactly its
table of cycle holonomies: a full `↔`, with the backward direction
witnessed by an explicit gauge built from the two tree holonomies. -/
theorem determination (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (θ₁ θ₂ : V → V → Circle) :
    (∃ h : V → Circle, θ₂ = gaugeConn h θ₁)
      ↔ ∀ i j, cycleHol par depth θ₁ i j
          = cycleHol par depth θ₂ i j := by
  constructor
  · rintro ⟨h, rfl⟩
    intro i j
    exact (cycleHol_gauge r par depth hdepth_r hstep h θ₁ i j).symm
  · intro h
    have hnorm : normalConn par depth θ₁ = normalConn par depth θ₂ := by
      funext i j
      rw [normalConn_eq_cycleHol, normalConn_eq_cycleHol, h i j]
    refine ⟨(treeHol par depth θ₂)⁻¹ * treeHol par depth θ₁, ?_⟩
    calc θ₂ = gaugeConn (treeHol par depth θ₂)⁻¹
            (normalConn par depth θ₂) :=
          eq_gaugeConn_inv_normalConn par depth θ₂
      _ = gaugeConn (treeHol par depth θ₂)⁻¹
            (normalConn par depth θ₁) := by
          rw [hnorm]
      _ = gaugeConn ((treeHol par depth θ₂)⁻¹ * treeHol par depth θ₁)
            θ₁ := by
          simp only [normalConn, ← gaugeConn_comp]

/-! ## §5. Uniqueness of the normal form, the readings, the weld

The normal form is not merely *a* tree-trivial representative: §5's
first theorem says it is the only one, so "gauge-equivalence class"
and "normal form" and "cycle-holonomy table" are three names for one
object. The readings corollary then restates B2/B3/B4′ in this
brick's terms, and `cycleHol_one` is the weld check: at zero field
every fundamental-cycle holonomy is trivial. -/

/-- A connection trivial on every tree edge has trivial tree
holonomy at every vertex: each factor of `treeHol` is a tree-edge
value read in the reverse direction, hence `1` by antisymmetry and
triviality. -/
theorem treeHol_eq_one_of_trivial (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    {θ : V → V → Circle} (hθ : ∀ i j, θ j i = (θ i j)⁻¹)
    (htriv : ∀ v : V, v ≠ r → θ v (par v) = 1) (v : V) :
    treeHol par depth θ v = 1 := by
  apply Finset.prod_eq_one
  intro n hn
  have hn' : n < depth v := Finset.mem_range.mp hn
  have hdep : depth (par^[n] v) + n = depth v :=
    depth_iterate_par r par depth hdepth_r hstep n v hn'.le
  have hu : par^[n] v ≠ r := by
    intro h
    rw [h, hdepth_r] at hdep
    omega
  have h2 : par^[n + 1] v = par (par^[n] v) := by
    rw [show n + 1 = 1 + n from Nat.add_comm n 1,
      Function.iterate_add_apply, Function.iterate_one]
  rw [h2, hθ (par^[n] v) (par (par^[n] v)), htriv _ hu, inv_one]

/-- **Uniqueness of the normal form**: a tree-trivial connection
gauge-equivalent to `θ` *is* `normalConn θ`. Gauge fixing on the
tree has exactly one output per gauge class. -/
theorem normalConn_unique (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    {θ θ' : V → V → Circle} (hθ' : ∀ i j, θ' j i = (θ' i j)⁻¹)
    {g : V → Circle} (hg : θ' = gaugeConn g θ)
    (htriv : ∀ v : V, v ≠ r → θ' v (par v) = 1) :
    θ' = normalConn par depth θ := by
  have hT : treeHol par depth θ' = 1 :=
    funext fun v =>
      treeHol_eq_one_of_trivial r par depth hdepth_r hstep hθ' htriv v
  have h1 : normalConn par depth θ' = θ' := by
    show gaugeConn (treeHol par depth θ') θ' = θ'
    rw [hT, gaugeConn_one]
  have h2 : normalConn par depth θ' = normalConn par depth θ := by
    funext i j
    rw [normalConn_eq_cycleHol, normalConn_eq_cycleHol, hg]
    exact cycleHol_gauge r par depth hdepth_r hstep g θ i j
  rw [← h1]
  exact h2

/-- **The readings package, holonomy form** (B4′'s
`gaugeClass_readings` with the hypothesis traded up from gauge
equivalence to cycle-holonomy equality, via `determination`):
connections with the same fundamental-cycle holonomies have the
same face holonomies, the same spectrum of `magLin w ·`, and the
same heat trace at every time. The bridge's three readings are
functions of the cycle-holonomy table. -/
theorem cycleHol_readings {F : Type*} (bd : F → GraphFace V)
    (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (w : V → V → ℝ) (θ₁ θ₂ : V → V → Circle)
    (h : ∀ i j, cycleHol par depth θ₁ i j
      = cycleHol par depth θ₂ i j)
    (f : F) (μ : ℂ) (t : ℝ) :
    faceHol bd θ₂ f = faceHol bd θ₁ f
      ∧ (Module.End.HasEigenvalue (magLin w θ₂) μ
          ↔ Module.End.HasEigenvalue (magLin w θ₁) μ)
      ∧ magHeatTrace w θ₂ t = magHeatTrace w θ₁ t := by
  obtain ⟨g, hg⟩ := (determination r par depth hdepth_r hstep θ₁ θ₂).mpr h
  subst hg
  exact ⟨faceHol_gauge bd g θ₁ f, magLin_gauge_hasEigenvalue w g θ₁ μ,
    magHeatTrace_gauge w g θ₁ t⟩

/-- **Weld check (charter A2)**: at `θ ≡ 1` — the zero field of the
landed Bridge exhibit — every fundamental-cycle holonomy is `1`, as
S4 requires: the general statement specializes to the exhibit's
trivial flux table. -/
theorem cycleHol_one (par : V → V) (depth : V → ℕ) (i j : V) :
    cycleHol par depth (fun _ _ => 1) i j = 1 := by
  have hT : ∀ v, treeHol par depth (fun _ _ => 1) v = 1 := fun v =>
    Finset.prod_eq_one fun n _ => rfl
  simp [cycleHol, hT]

end ThetLogos
