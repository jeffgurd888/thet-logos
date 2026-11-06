import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import ThetLogos.RLP1PhiLayer
import ThetLogos.RLP1Stationarity

/-!
# ThetLogos.RLP1Successor — RL-P1, Brick 3: the rest-start successor
exhibit (TW-S6) — SECONDARY / UNGRADED

## STATUS — READ FIRST (the closure is on the face)

This module formalizes, as corpus mathematics, exactly one item:
**TW-S6**, the rest-start successor exhibit of the Gate 4
derivation report (`rl-p1-gate4-derivation-2026-11-05.md`, §1.2 and
§8 item 2), for the mechanics registered as **RL-P1** (Gate 1
pre-registration v1, frozen 2026-11-05; v2,
`rl-p1-gate1-preregistration-v2-2026-11-05.md`). It builds on
Brick 1 (`ThetLogos.RLP1PhiLayer`: the seat package and
TW-P1..TW-P7) and Brick 2 (`ThetLogos.RLP1Stationarity`: the
action, the local expression, (ST), and TW-S1..TW-S5).

**TW-S6 is an EXHIBIT, graded SECONDARY / UNGRADED** at its
registration (Gate 4 §1.2; v2 §2.3), and it ships under that grade
here: it is recorded because v2 §2.3 names this successor set
available to audits as a secondary consistency exhibit; per v2
§2.3 it is **not a compared object**, and nothing in the Gate 4
verdict uses it. No statement in this module upgrades that grade.

**The gravity candidacy of RL-P1 is CLOSED.** At Gate 4 the frozen
shadow test (v2 §2) was run exactly as frozen, in exact rational
arithmetic, and shape agreement failed on both registered cases:
**K-RLP1-SHADOW FIRED.** The recorded verdict (v1 §6, pre-written)
is:

> **RL-P1 is a mechanics, not a gravity candidate.**

Per the registration (P-D2), that kill is final for RL-P1 as
registered; Gates 5–8 do not run on it. This module is built — on
Jeff's explicit decision of 2026-11-05 — **as corpus mechanics
only**, decoupled from any Dial-2 candidacy. There is **no Dial-2
language anywhere in this module**: no statement here is evidence
for, or a step toward, any gravity claim, and no statement here is
a response law. **NO CLAIM; dials 0/4; Dial 2 = 0.**

Register discipline (v1 §1, §2): everything below is **Register A
vocabulary only** — the seat of Brick 1, the step cost `ι`, the
local expression, the coupling sum `Φ`. Per rider **R-G2F2** (v2
§3): the minus sign in `Φ` and the stationarity-as-local-
minimization form are **declared conventions** of the primitive;
nothing in this module presents any lean of the stationary set as
derived attraction. Two further scope facts are part of the
registration and are kept on the face: stationarity (ST) is a
**system of inequalities, not an evolution law** — the successor
set below is a *set of admissible next sites* cut out by an
inequality system, not the output of any recursion or response
function; and **target (a) is UNGRADED — DESIGN PENDING**
(ODP-RLP1-FRAME): no frame data, variation class, or
Euler-realization content occurs here, and K-RLP1-EULER is not
armed.

## What is here

- §1: the successor predicate of TW-S6 — `z` can serve as the
  third site of a rest-start path `x₀ = x₁ = s` stationary at
  `t = 1` — and the exhibit theorem itself: stationarity at
  `t = 1` of a rest-start path ending in `z` holds iff `s`
  minimizes `w ↦ ι(w, s) + ι(z, w) + Φ(ρ, w)`, the local expression
  at neighbours `(s, z)` (Gate 4 §1.2: "Proof: (ST) at `t = 1`").
  Two further readings: the membership reading — `z` is a
  successor of `s` iff the constant path at `s`, varied at
  `t = 2` to end at `z`, is stationary at `t = 1` (for every
  `m > 0`, every horizon `2 ≤ T`) — and the one true direction of
  the rest reading: if every site is a successor of `s`, the
  constant path at `s` is stationary at `t = 1`. (The converse
  of the rest reading is false in general — the constant path
  sees only the local expression at neighbours `(s, s)`, the
  successor condition at `z ≠ s` sees neighbours `(s, z)` — and
  §2's seat exhibits the failure; the registration claims
  neither direction.)
- §2: the exhibit seat of Gate 4 §9 deviation 2 — the path graph
  P₄ on `Fin 4` with its declared constants (`q = 1/2`, `τ = 1`,
  horizon `T = 2`, background `ρ = δ₁`, all declared on the face
  of the Gate 4 exhibit, `stationarity_exhibit.py`) — and the
  successor set at `s = 1` on that seat, computed exactly:
  `{0, 1, 2}`. Site `3` is excluded, with the exact margin
  `1/4` (the local expression at `w = 3` exceeds the minimum at
  `w = 1` by `1/4`).

NOT here: target (a) in any form (see above); any shadow or
dictionary object (that was the audit's comparison standard,
closed at Gate 4); any E1–E7 content beyond the successor reading
of the exhibit seat (E5's rest criterion is TW-S5, Brick 2; E4 is
its sufficient condition; the successor content of the exhibit is
exactly §2 above).

Axiom audit: headline theorems are checked at the end of the file
against the standard three (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. TW-S6 — the rest-start successor exhibit -/

/-- The **rest-start successor predicate** of TW-S6 (Gate 4 §1.2):
`z` can serve as `x₂` of a rest-start path `x₀ = x₁ = s` that is
stationary at `t = 1` — by the registered statement, exactly when
`s` minimizes `w ↦ ι(w, s) + ι(z, w) + Φ(ρ, w)`, the local
expression at neighbours `(s, z)`. A set of admissible next sites
cut out by an inequality system; not the output of a recursion
(see the header). -/
def rlp1RestSucc (s : RLP1Seat V) (q τ : ℝ) (ρ : V → ℝ)
    (v₀ z : V) : Prop :=
  ∀ w : V, rlp1LocalExpr s q τ ρ v₀ z v₀
    ≤ rlp1LocalExpr s q τ ρ v₀ z w

/-- **TW-S6 (rest-start successor exhibit — SECONDARY,
UNGRADED).** For a path `x` with `x 0 = x 1 = v₀` and `x 2 = z`
(at any horizon `T` with `2 ≤ T`), `x` is stationary at `t = 1`
iff `z` is a rest-start successor of `v₀`. The path enters only
through its first three values: stationarity at `t = 1` reads
the neighbours `x 0, x 2` and the varied site `x 1`. *Proof
(Gate 4 §1.2):* (ST) at `t = 1` (Brick 2's TW-S1,
`rlp1StationaryAt_iff`). -/
theorem rlp1StationaryAt_one_two_iff_restSucc (s : RLP1Seat V)
    (q τ m : ℝ) (hm : 0 < m) (ρ : V → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (x : ℕ → V) (v₀ z : V) (hx0 : x 0 = v₀) (hx1 : x 1 = v₀)
    (hx2 : x 2 = z) :
    rlp1StationaryAt s q τ m ρ T x 1
      ↔ rlp1RestSucc s q τ ρ v₀ z := by
  have hsub : (1 : ℕ) - 1 = 0 := rfl
  rw [rlp1StationaryAt_iff s q τ m hm ρ T x le_rfl (by omega),
    hsub, hx0, hx1, hx2]
  exact Iff.rfl

/-- **TW-S6, rest reading (one direction).** If every site is a
rest-start successor of `v₀`, then the constant path at `v₀` is
stationary at `t = 1` (any horizon `T` with `2 ≤ T`): the
successor condition at `z = v₀` is exactly the `t = 1` instance
of the rest condition of TW-S5. The converse does **not** hold
in general — stationarity of the constant path constrains only
the local expression at neighbours `(v₀, v₀)`, while the
successor condition at `z ≠ v₀` constrains the local expression
at neighbours `(v₀, z)`; see the counterexample recorded after
`pathSeat4_restSucc_delta_one` in §2, where the constant path at
`1` rests on P₄ but site `3` is not a successor of `1`. The
registered TW-S6 makes neither direction of this path-level
equivalence; this is the one direction that is true. -/
theorem rlp1StationaryAt_const_one_two_of_restSucc (s : RLP1Seat V)
    (q τ m : ℝ) (hm : 0 < m) (ρ : V → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (v₀ : V) (h : ∀ z : V, rlp1RestSucc s q τ ρ v₀ z) :
    rlp1StationaryAt s q τ m ρ T (fun _ => v₀) 1 :=
  (rlp1StationaryAt_one_two_iff_restSucc s q τ m hm ρ T hT
    (fun _ => v₀) v₀ v₀ rfl rfl rfl).mpr (h v₀)

/-- **TW-S6, membership reading.** `z` is a rest-start successor
of `v₀` iff the constant path at `v₀`, varied at `t = 2` to end
at `z`, is stationary at `t = 1` — for every `m > 0` and every
horizon `T` with `2 ≤ T`. (The variation at `t = 2` is outside
the index `t = 1` at which stationarity is tested; the successor
condition is exactly what that stationarity sees.) -/
theorem rlp1RestSucc_mem_iff (s : RLP1Seat V) (q τ : ℝ)
    (ρ : V → ℝ) (v₀ z : V) :
    rlp1RestSucc s q τ ρ v₀ z
      ↔ ∀ (m : ℝ), 0 < m → ∀ (T : ℕ), 2 ≤ T →
          rlp1StationaryAt s q τ m ρ T
            (Function.update (fun _ => v₀) 2 z) 1 := by
  constructor
  · intro h m hm T hT
    exact (rlp1StationaryAt_one_two_iff_restSucc s q τ m hm ρ T
      hT (Function.update (fun _ => v₀) 2 z) v₀ z
      (by simp) (by simp) (Function.update_self ..)).mpr h
  · intro h
    exact (rlp1StationaryAt_one_two_iff_restSucc s q τ 1 one_pos
      ρ 2 le_rfl (Function.update (fun _ => v₀) 2 z) v₀ z
      (by simp) (by simp) (Function.update_self ..)).mp
      (h 1 one_pos 2 le_rfl)

/-! ## §2. The exhibit seat P₄ and its successor set at `s = 1`

The seat of Gate 4 §9 deviation 2's secondary exhibit
(`stationarity_exhibit.py`): the path graph on four sites, with
the exhibit's declared constants `q = 1/2`, `τ = 1`, horizon
`T = 2`, background `ρ = δ₁` — declared on the exhibit's face
there and carried unchanged here. -/

/-- The distance on the 4-site path: `|a − b|` on values. -/
def pathDist4 (x y : Fin 4) : ℕ := rlp1NatDist x.val y.val

theorem pathDist4_symm (x y : Fin 4) :
    pathDist4 x y = pathDist4 y x :=
  rlp1NatDist_symm x.val y.val

theorem pathDist4_self (x : Fin 4) : pathDist4 x x = 0 :=
  rlp1NatDist_self x.val

theorem pathDist4_triangle (x y z : Fin 4) :
    pathDist4 x z ≤ pathDist4 x y + pathDist4 y z :=
  rlp1NatDist_triangle x.val y.val z.val

/-- The unit weights of the P₄ seat: `1` on adjacent sites, `0`
elsewhere (the `Fin 8` pattern of Brick 1 at `Fin 4`). -/
def pathWeights4 (x y : Fin 4) : ℝ :=
  if pathDist4 x y = 1 then 1 else 0

theorem pathWeights4_symm :
    ∀ x y, pathWeights4 x y = pathWeights4 y x := by
  intro x y
  by_cases h : pathDist4 x y = 1
  · have h' : pathDist4 y x = 1 := by rw [pathDist4_symm]; exact h
    simp [pathWeights4, h, h']
  · have h' : pathDist4 y x ≠ 1 := by rw [pathDist4_symm]; exact h
    simp [pathWeights4, h, h']

theorem pathWeights4_diag : ∀ x, pathWeights4 x x = 0 := by
  intro x; simp [pathWeights4, pathDist4_self]

theorem pathWeights4_nonneg : ∀ x y, 0 ≤ pathWeights4 x y := by
  intro x y; unfold pathWeights4; split_ifs <;> norm_num

theorem pathWeights4_ne_zero_iff (x y : Fin 4) :
    pathWeights4 x y ≠ 0 ↔ pathDist4 x y = 1 := by
  by_cases h : pathDist4 x y = 1 <;> simp [pathWeights4, h]

/-- Adjacency in the P₄ seat graph is unit distance. -/
theorem pathAdj4_iff (hs : ∀ x y, pathWeights4 x y = pathWeights4 y x)
    (hd : ∀ x, pathWeights4 x x = 0) (x y : Fin 4) :
    (rlp1GraphOf pathWeights4 hs hd).Adj x y ↔ pathDist4 x y = 1 :=
  pathWeights4_ne_zero_iff x y

/-- Every walk in the P₄ seat graph has length at least the
distance of its endpoints. -/
theorem pathDist4_le_of_walk
    (hs : ∀ x y, pathWeights4 x y = pathWeights4 y x)
    (hd : ∀ x, pathWeights4 x x = 0) {x y : Fin 4}
    (p : (rlp1GraphOf pathWeights4 hs hd).Walk x y) :
    pathDist4 x y ≤ p.length := by
  induction p with
  | nil => simp [pathDist4_self]
  | @cons u v w h p ih =>
    have h1 : pathDist4 u v = 1 := (pathAdj4_iff hs hd u v).mp h
    have htri : pathDist4 u w ≤ pathDist4 u v + pathDist4 v w :=
      pathDist4_triangle u v w
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Every pair of sites of the P₄ seat is joined by a walk of
length exactly the distance (step one site toward the target). -/
theorem pathWalk4 (hs : ∀ x y, pathWeights4 x y = pathWeights4 y x)
    (hd : ∀ x, pathWeights4 x x = 0) (x y : Fin 4) :
    ∃ p : (rlp1GraphOf pathWeights4 hs hd).Walk x y,
      p.length = pathDist4 x y := by
  suffices h : ∀ n (x y : Fin 4), pathDist4 x y = n →
      ∃ p : (rlp1GraphOf pathWeights4 hs hd).Walk x y,
        p.length = n by
    exact h _ x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn
    by_cases hxy : x = y
    · have hn0 : n = 0 := by
        rw [← hn, hxy, pathDist4_self]
      subst hn0
      subst hxy
      exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.length_nil⟩
    · have hne : x.val ≠ y.val := fun hv => hxy (Fin.ext hv)
      have hn1 : 1 ≤ n := by
        have h0 : pathDist4 x y ≠ 0 := by
          show rlp1NatDist x.val y.val ≠ 0
          exact rlp1NatDist_eq_zero.not.mpr hne
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨x', hx'v⟩ : ∃ z : Fin 4, z.val = x.val + 1 :=
          ⟨⟨x.val + 1, by omega⟩, rfl⟩
        have hstep : pathDist4 x x' = 1
            ∧ pathDist4 x' y + 1 = pathDist4 x y := by
          constructor
          · show rlp1NatDist x.val x'.val = 1
            rw [hx'v]; unfold rlp1NatDist; omega
          · show rlp1NatDist x'.val y.val + 1 = rlp1NatDist x.val y.val
            rw [hx'v]; unfold rlp1NatDist; omega
        have hadj : (rlp1GraphOf pathWeights4 hs hd).Adj x x' :=
          (pathAdj4_iff hs hd x x').mpr hstep.1
        obtain ⟨p', hp'⟩ := ih (n - 1) (by omega) x' y (by omega)
        exact ⟨SimpleGraph.Walk.cons hadj p', by
          rw [SimpleGraph.Walk.length_cons, hp']; omega⟩
      · obtain ⟨x', hx'v⟩ : ∃ z : Fin 4, z.val = x.val - 1 :=
          ⟨⟨x.val - 1, by omega⟩, rfl⟩
        have hstep : pathDist4 x x' = 1
            ∧ pathDist4 x' y + 1 = pathDist4 x y := by
          constructor
          · show rlp1NatDist x.val x'.val = 1
            rw [hx'v]; unfold rlp1NatDist; omega
          · show rlp1NatDist x'.val y.val + 1 = rlp1NatDist x.val y.val
            rw [hx'v]; unfold rlp1NatDist; omega
        have hadj : (rlp1GraphOf pathWeights4 hs hd).Adj x x' :=
          (pathAdj4_iff hs hd x x').mpr hstep.1
        obtain ⟨p', hp'⟩ := ih (n - 1) (by omega) x' y (by omega)
        exact ⟨SimpleGraph.Walk.cons hadj p', by
          rw [SimpleGraph.Walk.length_cons, hp']; omega⟩

/-- The P₄ seat graph is connected. -/
theorem pathConnected4
    (hs : ∀ x y, pathWeights4 x y = pathWeights4 y x)
    (hd : ∀ x, pathWeights4 x x = 0) :
    (rlp1GraphOf pathWeights4 hs hd).Connected := by
  constructor
  · intro x y
    obtain ⟨p, -⟩ := pathWalk4 hs hd x y
    exact ⟨p⟩

/-- The graph distance of the P₄ seat is `|x − y|`. -/
theorem pathGraph4_dist
    (hs : ∀ x y, pathWeights4 x y = pathWeights4 y x)
    (hd : ∀ x, pathWeights4 x x = 0) (x y : Fin 4) :
    (rlp1GraphOf pathWeights4 hs hd).dist x y = pathDist4 x y := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := pathWalk4 hs hd x y
    rw [← hp]
    exact SimpleGraph.dist_le p
  · obtain ⟨p, hp⟩ := (pathConnected4 hs hd).exists_walk_length_eq_dist
      (u := x) (v := y)
    rw [← hp]
    exact pathDist4_le_of_walk hs hd p

/-- The path seat P₄ as a packaged seat. -/
def pathSeat4 : RLP1Seat (Fin 4) where
  w := pathWeights4
  symm := pathWeights4_symm
  nonneg := pathWeights4_nonneg
  diag := pathWeights4_diag
  connected := pathConnected4 pathWeights4_symm pathWeights4_diag

/-- The seat distance of P₄ is `|x − y|`. -/
theorem pathSeat4_dist (x y : Fin 4) :
    pathSeat4.dist x y = pathDist4 x y :=
  pathGraph4_dist _ _ x y

/-- Φ of the exhibit background `δ₁` on P₄, closed form:
`Φ(δ₁, x) = −(1/2)^{|x − 1|}` — the values of the Gate 4 exhibit
(`Phi_values`: `−1/2, −1, −1/2, −1/4` at sites `0, 1, 2, 3`). -/
theorem pathSeat4_phi_delta_one (x : Fin 4) :
    rlp1Phi pathSeat4 (1/2 : ℝ) (rlp1Delta 1) x
      = -((1/2 : ℝ) ^ pathDist4 x 1) := by
  rw [rlp1Phi_delta]
  show -((1/2 : ℝ) ^ pathSeat4.dist x 1) = -((1/2 : ℝ) ^ pathDist4 x 1)
  rw [pathSeat4_dist]

/-- The local expression of the exhibit seat, evaluated: at
neighbours `(1, z)` and site `w`,
`L(z, w) = (d(w,1)² + d(z,w)²)/2 − (1/2)^{d(w,1)}`, with the
seat distances and `Φ(δ₁, ·)` in closed form. -/
theorem pathSeat4_localExpr_eq (z w : Fin 4) :
    rlp1LocalExpr pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 z w
      = ((pathDist4 w 1 : ℝ) ^ 2 + (pathDist4 z w : ℝ) ^ 2) / 2
        - (1/2 : ℝ) ^ pathDist4 w 1 := by
  unfold rlp1LocalExpr rlp1Iota
  rw [pathSeat4_phi_delta_one]
  rw [pathSeat4_dist z w, pathSeat4_dist w 1]
  ring

/-- The local-expression table of the exhibit seat at `w = 1`
(the minimizing site): at neighbours `(1, z)`, the value at
`w = 1` is `−1` for `z = 1`, `−1/2` for `z ∈ {0, 2}`, and
`1` for `z = 3`. (Values as computed from the seat's own
definitions by `pathSeat4_localExpr_eq`; an earlier draft of
this lane carried different table values, which `norm_num`
correctly refused — the refusal, not the arithmetic, was the
blocker, and the corrected tables are what is proved here.) -/
theorem pathSeat4_localExpr_at_one (z : Fin 4) :
    rlp1LocalExpr pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 z 1
      = if z = 1 then -1 else if z = 3 then 1 else -1/2 := by
  fin_cases z
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]

/-- The local-expression table of the exhibit seat at `w = 3`:
at neighbours `(1, z)`, the value at `w = 3` is `25/4`,
`15/4`, `9/4`, `7/4` for `z = 0, 1, 2, 3` respectively. -/
theorem pathSeat4_localExpr_at_three (z : Fin 4) :
    rlp1LocalExpr pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 z 3
      = if z = 0 then 25/4 else if z = 1 then 15/4
        else if z = 2 then 9/4 else 7/4 := by
  fin_cases z
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]
  · rw [pathSeat4_localExpr_eq]
    norm_num [pathDist4, rlp1NatDist]

/-- The local expression at neighbours `(1, 3)`, site `w = 2`:
the value `1/2`. Against the value `1` at the minimizing site
`w = 1` (`pathSeat4_localExpr_at_one`), this is the comparison
that excludes site `3` from the successor set of `1`, with
exact margin `1/2`. -/
theorem pathSeat4_localExpr_three_two :
    rlp1LocalExpr pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 3 2 = 1/2 := by
  rw [pathSeat4_localExpr_eq]
  norm_num [pathDist4, rlp1NatDist]

/-- **TW-S6 on the exhibit seat (SECONDARY / UNGRADED).** On P₄
with the exhibit's declared constants (`q = 1/2`, `τ = 1`,
background `δ₁`), the rest-start successors of the site `s = 1` —
the global minimizer of `Φ(δ₁, ·)` on this seat (Gate 4 exhibit,
`argmin_Phi_site = 1`) — are exactly the sites `0, 1, 2`: site
`3` fails, with exact margin `1/2` (the local expression at
neighbours `(1, 3)` takes the value `1/2` at `w = 2` against
`1` at the minimizing site `w = 1`, by the tables above).
Computed here from the seat's own definitions; the exhibit's
Python record (`exhibit-results.json`) is the probe this
formalizes, and the two agree. -/
theorem pathSeat4_restSucc_delta_one (z : Fin 4) :
    rlp1RestSucc pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 z
      ↔ z = 0 ∨ z = 1 ∨ z = 2 := by
  have hval : ∀ (z w : Fin 4),
      rlp1LocalExpr pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 z w
        = ((pathSeat4.dist w 1 : ℝ) ^ 2
            + (pathSeat4.dist z w : ℝ) ^ 2) / 2
          + -((1/2 : ℝ) ^ pathDist4 w 1) := by
    intro z w
    unfold rlp1LocalExpr rlp1Iota
    rw [pathSeat4_phi_delta_one]
    ring
  fin_cases z
  · refine ⟨fun _ => Or.inl rfl, fun _ w => ?_⟩
    rw [hval, hval]
    fin_cases w <;> simp only [pathSeat4_dist, pathDist4] <;>
      norm_num [rlp1NatDist]
  · refine ⟨fun _ => Or.inr (Or.inl rfl), fun _ w => ?_⟩
    rw [hval, hval]
    fin_cases w <;> simp only [pathSeat4_dist, pathDist4] <;>
      norm_num [rlp1NatDist]
  · refine ⟨fun _ => Or.inr (Or.inr rfl), fun _ w => ?_⟩
    rw [hval, hval]
    fin_cases w <;> simp only [pathSeat4_dist, pathDist4] <;>
      norm_num [rlp1NatDist]
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have hle := h 2
      rw [hval, hval] at hle
      norm_num [pathSeat4_dist, pathDist4, rlp1NatDist] at hle
    · rcases h with h0 | h1 | h2 <;> simp_all

/-- **The rest reading's converse fails on the exhibit seat
(SECONDARY / UNGRADED).** The constant path at `1` on P₄ (with
the exhibit's constants, horizon `T = 2`) **is** stationary at
`t = 1` — `1` is the global minimizer of `Φ(δ₁, ·)`, so it rests
by TW-S5's sufficient condition — yet **not** every site is a
rest-start successor of `1`: site `3` is not
(`pathSeat4_restSucc_delta_one`). So "the constant path at `s`
is stationary at `t = 1`" does not imply "every site is a
successor of `s`": the two conditions read the local expression
at different neighbours, `(s, s)` versus `(s, z)`. Recorded so
the one-directional theorem of §1
(`rlp1StationaryAt_const_one_two_of_restSucc`) is never
over-read as an equivalence; the registered TW-S6 claims
neither direction of it. -/
theorem pathSeat4_const_stationary_not_all_succ :
    rlp1StationaryAt pathSeat4 (1/2 : ℝ) 1 1 (rlp1Delta 1) 2
        (fun _ => (1 : Fin 4)) 1
      ∧ ¬ ∀ z : Fin 4,
          rlp1RestSucc pathSeat4 (1/2 : ℝ) 1 (rlp1Delta 1) 1 z := by
  refine ⟨?_, ?_⟩
  · apply rlp1StationaryAt_const_of_phi_min pathSeat4 (1/2 : ℝ) 1 1
      one_pos one_pos (rlp1Delta 1) 2 1 _ le_rfl one_lt_two
    intro z
    rw [pathSeat4_phi_delta_one, pathSeat4_phi_delta_one]
    fin_cases z <;> simp only [pathDist4] <;> norm_num [rlp1NatDist]
  · intro h
    have h3 := (pathSeat4_restSucc_delta_one 3).mp (h 3)
    simp at h3

/-! ## Axiom audit (headline theorems)

Expected: exactly the standard three (`propext`,
`Classical.choice`, `Quot.sound`) for every headline below. -/

#print axioms rlp1StationaryAt_one_two_iff_restSucc
#print axioms rlp1StationaryAt_const_one_two_of_restSucc
#print axioms rlp1RestSucc_mem_iff
#print axioms pathSeat4_localExpr_eq
#print axioms pathSeat4_localExpr_three_two
#print axioms pathSeat4_localExpr_at_one
#print axioms pathSeat4_localExpr_at_three
#print axioms pathSeat4_restSucc_delta_one
#print axioms pathSeat4_const_stationary_not_all_succ

end ThetLogos
