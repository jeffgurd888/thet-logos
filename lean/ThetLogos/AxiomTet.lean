/-
# AXIOM TET — equality first: unbroken agreement on a connected web forces one value

Brick: AXIOM TET (Jeff's name; expanded title: "Grand Unified Axiom
Zero - Invincible Unity and Universal Equality"). Commission:
Jeff, 2026-11-03 02:00 EST — "run it now", lifting his heavy-data
hold for this item only. Built from the frozen scope
`axiom-zero-equality-first-scoping-2026-11-03.md` (Option B) and
the first-primitives model `grand-unified-axiom-zero-model-2026-11-03.md`.

**What this module proves — and all it proves.** Start from
equality, not from numerals. The front door is the model's
P0–P5 in finite dress: a web (a `SimpleGraph`), positive *need
weights* on its edges, a state `f`, and — on a finite web — the
break energy `B_w(f) = ∑_{edges} w_e (f v − f u)²`. Three pins:

* **AZ-1 (equality propagation).** On a connected web, a state of
  ANY type that agrees across every edge is constant: local
  unbroken equality propagates along paths to one global value.
  No finiteness is used — this is the pure core, stated first.
* **AZ-2W (weighted zero-break).** On a finite connected web,
  with positive need weights, `B_w(f) = 0 ↔ f` is constant.
  AZ-2 (the unweighted form) is the `w ≡ 1` corollary. Without
  connectedness the exact statement is per-component: zero break
  iff `f` agrees on every reachable pair — and the disconnected
  counterexample stands in-tree below as the K-AZ-DISC fence
  (the empty web on two sites: zero break, no global constant).
* **AZ-3 (one at every scale).** Discharged by the generality of
  AZ-1/AZ-2W plus the cycle family: Mathlib's `cycleGraph (n+1)`
  is connected for every `n`, so the constant characterization
  holds uniformly over all cycle sizes. That uniformity across
  finite sizes is the ONLY formal content this brick gives to
  "infinity": no literal `1 = ∞` statement is attempted (K-AZ-INF,
  fenced in the scope; the identity remains T5 doctrine).
* **AZ-5 (mirror seat, stretch).** On `ZMod (2n+1)`, the
  self-mirror equation `x = −x` has exactly one solution, `0` —
  the equality point of the mirror, unique because the modulus
  is odd. This is the same shape as Mirror-21's unique center.

**The Need Guard, on the face.** Axiom Zero's equality is
equality of LAW — the same unbreakable agreement rule at every
edge — NOT equality of allotment. Jeff's allocation law stands
untouched ("to each it's need not equality"; paired form:
"unbreakable unity and universal equality of need" — the
need-rule universal, the portions each their own). Formally the
guard is AZ-2W itself: the weights `w_e` are positive and
nowhere assumed equal, and the unity conclusion survives
*because* the weights are free to differ. One law; to each
edge, its need.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. Cabinet-tier finite brick;
no ladder rung claimed.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

-- The `haveI` in `zmod_self_neg_iff` is load-bearing (it registers the
-- `NeZero` instance the `ZMod.val` lemmas synthesize against); the style
-- linter's preference for `have` does not apply there.
set_option linter.style.haveILetI false

open Finset SimpleGraph

namespace ThetLogos

variable {V : Type*} (G : SimpleGraph V)

/-! ## The local break (model P5) and AZ-1: equality propagation

P0 (boundary/container) and P1 (adjacency) are the web `G` itself;
P2 (equality) is the agreement law the theorems quantify over;
P4 (state) is `f`. None of this section needs finiteness. -/

/-- P5, local: the squared break across an unordered edge. The
squared difference is symmetric in the endpoints, so it descends
to `Sym2 V` — an edge has a break before it has a direction. -/
noncomputable def diffSq (f : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => (f v - f u) ^ 2, fun a b => by ring⟩

theorem diffSq_mk (f : V → ℝ) (u v : V) : diffSq f s(u, v) = (f v - f u) ^ 2 := by
  simp [diffSq, Sym2.lift_mk]

theorem diffSq_nonneg (f : V → ℝ) (e : Sym2 V) : 0 ≤ diffSq f e := by
  induction e using Sym2.inductionOn with
  | hf u v => rw [diffSq_mk]; exact sq_nonneg _

/-- Agreement propagates along any walk: if `f` agrees across
every edge, it takes the same value at both ends of a walk.
Pure equality bookkeeping — no arithmetic, any value type. -/
theorem eq_of_walk {α : Type*} {f : V → α} (h : ∀ u v, G.Adj u v → f u = f v)
    {u v : V} (p : G.Walk u v) : f u = f v := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- **AZ-1 (equality propagation).** On a connected web, a state
of any type that respects every edge is constant: unbroken local
equality forces one global value. Connectedness is a hypothesis,
not decoration (see the fence example below). -/
theorem constant_of_adj_eq {α : Type*} {f : V → α} (hG : G.Connected)
    (h : ∀ u v, G.Adj u v → f u = f v) : ∃ c, ∀ v, f v = c := by
  obtain ⟨r⟩ := hG.nonempty
  exact ⟨f r, fun v => (eq_of_walk G h (hG.preconnected r v).some).symm⟩

/-- One edge-term of the break energy at a named edge: positive
need times a square. (Stated before finiteness enters: a single
term needs no sum.) -/
theorem breakTerm_mk_nonneg {w : Sym2 V → ℝ} (hw : ∀ u v, G.Adj u v → 0 < w s(u, v))
    (f : V → ℝ) {u v : V} (h : G.Adj u v) : 0 ≤ w s(u, v) * diffSq f s(u, v) :=
  mul_nonneg (hw u v h).le (diffSq_nonneg f _)

/-! ## The break energy (finite webs) and AZ-2W

Finiteness enters here, and only here: the energy is a finite
sum over the edge finset. The classical decidability instance
is local to this file — the energy's *membership* characterization
(`mem_edgeFinset`) is instance-independent, and every theorem
below speaks only through it. -/

variable [Fintype V]

attribute [local instance] Classical.propDecidable

/-- P0–P5 assembled: the break energy of a state `f` on the
finite web `G` with edge-indexed need weights `w` (model P3).
`B_w(f) = ∑_{edges} w_e · (f v − f u)²`. The weights are indexed
by the edge itself (`Sym2 V`), so no orientation is ever chosen;
positivity of the weights is a hypothesis of the theorems, not
of the definition, so that the fences (zero-weight bridges,
disconnected webs) can be stated against this same definition. -/
noncomputable def breakEnergy (w : Sym2 V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, w e * diffSq f e

/-- Every edge-term of the break energy is nonnegative. -/
theorem breakTerm_nonneg {w : Sym2 V → ℝ} (hw : ∀ u v, G.Adj u v → 0 < w s(u, v))
    (f : V → ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset) : 0 ≤ w e * diffSq f e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact breakTerm_mk_nonneg G hw f he

/-- P5, global sign: break energy is never negative (positive
needs, squared breaks, no cancellation). -/
theorem breakEnergy_nonneg {w : Sym2 V → ℝ} (hw : ∀ u v, G.Adj u v → 0 < w s(u, v))
    (f : V → ℝ) : 0 ≤ breakEnergy G w f :=
  Finset.sum_nonneg (fun _e he => breakTerm_nonneg G hw f he)

/-- Zero break forces agreement across any single edge (the
positive need on that edge cannot be cancelled by anything:
every term is nonnegative, so a zero sum has zero terms). -/
theorem eq_of_breakEnergy_eq_zero {w : Sym2 V → ℝ}
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) {f : V → ℝ}
    (hf : breakEnergy G w f = 0) {u v : V} (h : G.Adj u v) : f u = f v := by
  have hf' : (∑ e ∈ G.edgeFinset, w e * diffSq f e) = 0 := hf
  have hterm : w s(u, v) * diffSq f s(u, v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun e he => breakTerm_nonneg G hw f he)).mp hf' _
      (by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet])
  rw [diffSq_mk] at hterm
  have hsq : (f v - f u) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with h1 | h1
    · exact absurd h1 (hw u v h).ne'
    · exact h1
  have hdiff : f v - f u = 0 := by rwa [sq_eq_zero_iff] at hsq
  exact (sub_eq_zero.mp hdiff).symm

/-- The per-component form, with NO connectedness assumed:
zero break iff `f` agrees on every reachable pair — one free
value per connected component, no more, no less. -/
theorem breakEnergy_eq_zero_iff_forall_reachable {w : Sym2 V → ℝ}
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (f : V → ℝ) :
    breakEnergy G w f = 0 ↔ ∀ u v, G.Reachable u v → f u = f v := by
  constructor
  · intro hf u v huv
    obtain ⟨p⟩ := huv
    exact eq_of_walk G (fun a b hab => eq_of_breakEnergy_eq_zero G hw hf hab) p
  · intro hreach
    show (∑ e ∈ G.edgeFinset, w e * diffSq f e) = 0
    apply Finset.sum_eq_zero
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hab : f a = f b := hreach a b he.reachable
      rw [diffSq_mk, ← hab]
      simp

/-- **AZ-2W (weighted zero-break iff unity).** On a connected
web, with positive need weights — each edge's own, nowhere
assumed equal — the break energy vanishes iff the state is one
global constant. This is the Need Guard as a theorem: the law
is one, and unity holds *with* non-flat portions, not by
flattening them. -/
theorem breakEnergy_eq_zero_iff_constant {w : Sym2 V → ℝ} (hG : G.Connected)
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (f : V → ℝ) :
    breakEnergy G w f = 0 ↔ ∃ c, ∀ v, f v = c := by
  rw [breakEnergy_eq_zero_iff_forall_reachable G hw f]
  constructor
  · intro hreach
    obtain ⟨r⟩ := hG.nonempty
    exact ⟨f r, fun v => hreach v r (hG.preconnected v r)⟩
  · rintro ⟨c, hc⟩ u v _
    rw [hc u, hc v]

/-- **AZ-2 (unweighted zero-break).** The flat-weight special
case `w ≡ 1` of AZ-2W — kept as its own statement because the
scope's AZ-2 names it; the general law is AZ-2W. -/
theorem breakEnergy_one_eq_zero_iff_constant (hG : G.Connected) (f : V → ℝ) :
    breakEnergy G (fun _ => 1) f = 0 ↔ ∃ c, ∀ v, f v = c :=
  breakEnergy_eq_zero_iff_constant G hG (fun _ _ _ => one_pos) f

/-- **The K-AZ-DISC fence, in-tree.** Without connectedness,
zero break does NOT force a global constant: on the empty web
over two sites every state has zero break (there are no edges
to break), and `![0, 1]` is a zero-break state that is not
constant. Connectedness in AZ-1/AZ-2W is load-bearing. -/
example : ∃ (w : Sym2 (Fin 2) → ℝ) (f : Fin 2 → ℝ),
    breakEnergy (⊥ : SimpleGraph (Fin 2)) w f = 0 ∧ ¬ ∃ c, ∀ v, f v = c := by
  refine ⟨fun _ => 1, ![0, 1], ?_, ?_⟩
  · simp only [breakEnergy, SimpleGraph.edgeFinset, SimpleGraph.edgeSet_bot,
      Set.toFinset_empty, Finset.sum_empty]
  · rintro ⟨c, hc⟩
    have h0 := hc 0
    have h1 := hc 1
    simp at h0 h1
    linarith

/-! ## AZ-3: one at every scale

AZ-3 is discharged by the generality of AZ-1/AZ-2W — neither
statement mentions a size — together with the cycle family
below: Mathlib's `cycleGraph (n + 1)` is connected for every
`n` (`cycleGraph_connected`), so the constant characterization
holds uniformly over all cycle sizes. No separate infinity
result is manufactured or needed; uniformity across finite
sizes is the whole formal content (K-AZ-INF). -/

/-- **AZ-3, propagation form.** For every `n`, an edge-respecting
state on the cycle `cycleGraph (n + 1)` is constant. -/
theorem cycle_constant_of_adj_eq {α : Type*} {n : ℕ} {f : Fin (n + 1) → α}
    (h : ∀ u v, (cycleGraph (n + 1)).Adj u v → f u = f v) : ∃ c, ∀ v, f v = c :=
  constant_of_adj_eq (cycleGraph (n + 1)) cycleGraph_connected h

/-- **AZ-3, zero-break form.** For every `n` and every choice of
positive need weights, a state on the cycle `cycleGraph (n + 1)`
has zero break energy iff it is constant. -/
theorem cycle_breakEnergy_eq_zero_iff_constant {n : ℕ} {w : Sym2 (Fin (n + 1)) → ℝ}
    (hw : ∀ u v, (cycleGraph (n + 1)).Adj u v → 0 < w s(u, v)) (f : Fin (n + 1) → ℝ) :
    breakEnergy (cycleGraph (n + 1)) w f = 0 ↔ ∃ c, ∀ v, f v = c :=
  breakEnergy_eq_zero_iff_constant (cycleGraph (n + 1)) cycleGraph_connected hw f

/-! ## AZ-5: the mirror seat (stretch) -/

/-- **AZ-5 (mirror seat).** On `ZMod (2n + 1)`, the self-mirror
equation `x = −x` holds iff `x = 0`: the mirror's equality point
is unique because the modulus is odd (`2` is coprime to
`2n + 1`, so `2x = 0` forces `x = 0`). The same shape as
Mirror-21's unique center, at every odd modulus. -/
theorem zmod_self_neg_iff (n : ℕ) (x : ZMod (2 * n + 1)) : x = -x ↔ x = 0 := by
  constructor
  · intro h
    have h2 : (2 : ZMod (2 * n + 1)) * x = 0 := by linear_combination h
    haveI : NeZero (2 * n + 1) := ⟨by omega⟩
    have hx : x = (x.val : ZMod (2 * n + 1)) := (ZMod.natCast_zmod_val x).symm
    have hdvd : (2 * n + 1) ∣ 2 * x.val := by
      have h2' : ((2 * x.val : ℕ) : ZMod (2 * n + 1)) = 0 := by
        rw [Nat.cast_mul, Nat.cast_ofNat, ← hx]
        exact h2
      exact (ZMod.natCast_eq_zero_iff (2 * x.val) (2 * n + 1)).mp h2'
    have hcop : Nat.Coprime (2 * n + 1) 2 := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by rintro ⟨k, hk⟩; omega)
    have hdvd' : (2 * n + 1) ∣ x.val := hcop.dvd_of_dvd_mul_left hdvd
    have hval : x.val = 0 := by
      rcases Nat.eq_zero_or_pos x.val with h0 | hpos
      · exact h0
      · have hle := Nat.le_of_dvd hpos hdvd'
        have hlt := ZMod.val_lt x
        omega
    rw [hx, hval, Nat.cast_zero]
  · intro h
    rw [h]
    simp

/-- AZ-5, uniqueness form: the self-mirror solution set on
`ZMod (2n + 1)` is exactly `{0}` — one equality point. -/
theorem zmod_self_neg_unique (n : ℕ) : {x : ZMod (2 * n + 1) | x = -x} = {0} := by
  ext x
  simp [zmod_self_neg_iff]

end ThetLogos
