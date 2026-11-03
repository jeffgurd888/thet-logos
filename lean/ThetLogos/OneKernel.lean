/-
# U-1 ONE KERNEL — weld the three kernel formalisms, demote Orthogonal

Brick: U-1 "One Kernel", the first brick of the unification line
(Jeff fired it by name, 2026-11-03: "Fire U-1 ONE KERNEL").
Scoping: `your_files/unification-scoping-2026-11-03.md` §2 (U-1),
whose headline finding this brick executes: the corpus already
proved its master kernel theorem three times in three general
formalisms — Bridge's dense-weight energy (`BridgeLaplacian`),
Axiom Tet's AZ-2W (`breakEnergy_eq_zero_iff_constant`), and
Partner's operator form — and one standalone kernel proof was
left, Orthogonal's O4+ (`lapSum_eq_zero_iff`). What was missing
is the *identifications*. This module builds them:

* **(a) The Bridge dictionary.** With `denseWeight G w` the
  dense weight of a web (the edge weight on adjacent pairs, `0`
  elsewhere), Bridge's quadratic form at that weight IS Axiom
  Tet's break energy — the same number, not a proportionality:
  `bridge_energy_eq_breakEnergy`. Bridge's constancy corollary
  then comes back through AZ-2W at *weaker* hypotheses than the
  original (`eq_const_of_energy_eq_zero` needed ALL off-diagonal
  conductances positive; here connectedness of the web plus
  per-edge positivity suffices): the corollary returns strictly
  stronger than the original.
* **(b) The Orthogonal identification.** In energy form, the
  break energy of the box product of two 21-cycles at unit
  weight is exactly Orthogonal's step energy
  (`breakEnergy_boxProd_cycle_eq`), hence `lapSum f = 0 ↔
  breakEnergy = 0` (`lapSum_eq_zero_iff_breakEnergy_boxProd`),
  and O4+ is demoted to a corollary of AZ-2W:
  `lapSum_eq_zero_iff_via_oneKernel` reproves the exact
  statement of `lapSum_eq_zero_iff` in a few lines routed
  through the master theorem (the original keeps its name and
  its seat; this is an additional route, not an edit).

**Kills, pre-registered in the scoping:** K-U1-DICT (the Bridge
energy does not reindex onto `edgeFinset` under `denseWeight` —
a convention mismatch that changes the kernel) and K-U1-BOX
(the `lapSum` kernel differs from the boxProd break-energy
kernel). Status reported in the landing dossier.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. A unified finite
combinatorics of the corpus's graph seats is not a unified
theory of physics: it derives no measured number, contains no
gravity object, proves no continuum limit, predicts nothing
external.
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import ThetLogos.BridgeLaplacian
import ThetLogos.AxiomTet
import ThetLogos.MirrorTwentyOneOrthogonalSpectral

open Finset SimpleGraph

namespace ThetLogos

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-! ## Part 0 — the ordered/unordered double count

Every energy dictionary in this brick passes through one
bookkeeping fact: summing a `Sym2`-valued quantity over all
ordered adjacent pairs counts each undirected edge exactly
twice. -/

/-- The double count: the ordered adjacent-pair sum of a
`Sym2` quantity is twice its sum over the edge finset. The
fiber of the quotient map `p ↦ s(p.1, p.2)` over an edge
`s(i, j)` is exactly the two orientations `{(i, j), (j, i)}`
(looplessness gives `i ≠ j`, so the pair is a genuine pair). -/
theorem sum_adj_apply_eq_two_mul_sum_edgeFinset (F : Sym2 V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then F s(i, j) else 0)
      = 2 * ∑ e ∈ G.edgeFinset, F e := by
  classical
  set s : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2) with hs_def
  have hmaps : ∀ p ∈ s, s(p.1, p.2) ∈ G.edgeFinset := by
    intro p hp
    rw [hs_def, Finset.mem_filter] at hp
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2
  have hfiber : ∀ e ∈ G.edgeFinset,
      (∑ p ∈ s with s(p.1, p.2) = e, F s(p.1, p.2)) = 2 * F e := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf i j =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hij : i ≠ j := he.ne
      have hflt : s.filter (fun p => s(p.1, p.2) = s(i, j)) = {(i, j), (j, i)} := by
        ext p
        simp only [Finset.mem_filter, hs_def, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        constructor
        · rintro ⟨hadj, hseq⟩
          rw [Sym2.eq, Sym2.rel_iff] at hseq
          rcases hseq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨by rw [h1, h2]; exact he, by rw [h1, h2]⟩
          · refine ⟨by rw [h1, h2]; exact he.symm, ?_⟩
            rw [h1, h2]
            exact Sym2.eq_swap
      rw [hflt, Finset.sum_pair]
      · rw [Sym2.eq_swap]; ring
      · intro hcon
        apply hij
        have := congrArg Prod.fst hcon
        simpa using this
  have h1 : (∑ e ∈ G.edgeFinset, ∑ p ∈ s with s(p.1, p.2) = e, F s(p.1, p.2))
      = ∑ p ∈ s, F s(p.1, p.2) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum] at h1
  have h2 : (∑ p ∈ s, F s(p.1, p.2))
      = ∑ i, ∑ j, if G.Adj i j then F s(i, j) else 0 := by
    have step1 : (∑ p ∈ s, F s(p.1, p.2))
        = ∑ p : V × V, if G.Adj p.1 p.2 then F s(p.1, p.2) else 0 := by
      rw [hs_def, Finset.sum_filter]
    rw [step1]
    exact Fintype.sum_prod_type _
  rw [h2] at h1
  exact h1.symm

/-! ## Part (a) — the Bridge ↔ AxiomTet dictionary -/

/-- The dense weight of a web: the edge weight `w s(i, j)` on
adjacent pairs, `0` elsewhere — the dictionary entry that lets
Bridge's dense formalism (`w : V → V → ℝ`) speak about a
`SimpleGraph` with `Sym2`-indexed weights. -/
noncomputable def denseWeight (G : SimpleGraph V) (w : Sym2 V → ℝ) : V → V → ℝ :=
  fun i j => if G.Adj i j then w s(i, j) else 0

omit [Fintype V] [DecidableEq V] in
theorem denseWeight_apply_adj {w : Sym2 V → ℝ} {i j : V} (h : G.Adj i j) :
    denseWeight G w i j = w s(i, j) :=
  ite_eq_left h

omit [Fintype V] [DecidableEq V] in
theorem denseWeight_apply_not_adj {w : Sym2 V → ℝ} {i j : V} (h : ¬ G.Adj i j) :
    denseWeight G w i j = 0 :=
  ite_eq_right h

omit [Fintype V] [DecidableEq V] in
/-- The dense weight is symmetric — the hypothesis Bridge's
energy identity spends — because adjacency is symmetric and
`s(i, j) = s(j, i)`. -/
theorem denseWeight_symm (w : Sym2 V → ℝ) :
    ∀ i j, denseWeight G w i j = denseWeight G w j i := by
  intro i j
  by_cases h : G.Adj i j
  · rw [denseWeight_apply_adj G h, denseWeight_apply_adj G h.symm, Sym2.eq_swap]
  · have h' : ¬ G.Adj j i := fun hh => h hh.symm
    rw [denseWeight_apply_not_adj G h, denseWeight_apply_not_adj G h']

/-- **The dictionary (a).** Bridge's quadratic form at the
dense weight of a web IS Axiom Tet's break energy of that
web — an equality of numbers, not a proportionality. Proof:
Bridge's `energy_identity` writes twice the form as the
ordered sum of weighted squared drops; the double count of
Part 0 reindexes that ordered sum onto `edgeFinset`, where
it is twice the break energy. -/
theorem bridge_energy_eq_breakEnergy (w : Sym2 V → ℝ) (f : V → ℝ) :
    (∑ i, f i * laplacianOp (denseWeight G w) f i) = breakEnergy G w f := by
  have hid := energy_identity (denseWeight G w) (denseWeight_symm G w) f
  have hdict : (∑ i, ∑ j, denseWeight G w i j * (f i - f j) ^ 2)
      = 2 * breakEnergy G w f := by
    have h := sum_adj_apply_eq_two_mul_sum_edgeFinset G (fun e => w e * diffSq f e)
    have hBE : breakEnergy G w f = ∑ e ∈ G.edgeFinset, w e * diffSq f e := rfl
    rw [hBE, ← h]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.Adj i j
    · rw [denseWeight_apply_adj G hij, ite_eq_left hij, diffSq_mk]
      have hsq : (f i - f j) ^ 2 = (f j - f i) ^ 2 := by ring
      rw [hsq]
    · rw [denseWeight_apply_not_adj G hij, ite_eq_right hij]
      simp
  linarith

/-- **The Bridge kernel, at AZ-2W's strength.** Zero Bridge
energy at a dense weight, on a connected web with positive
per-edge need weights, iff the state is constant — the
dictionary moves the whole kernel characterization across. -/
theorem bridge_energy_eq_zero_iff {w : Sym2 V → ℝ} (hG : G.Connected)
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (f : V → ℝ) :
    (∑ i, f i * laplacianOp (denseWeight G w) f i = 0) ↔ ∃ c, ∀ v, f v = c := by
  rw [bridge_energy_eq_breakEnergy]
  exact breakEnergy_eq_zero_iff_constant G hG hw f

/-- **Bridge's constancy corollary, strengthened.** The
original (`BridgeLaplacian.eq_const_of_energy_eq_zero`)
requires every off-diagonal conductance positive — complete
support. Routed through the dictionary and AZ-2W, the same
conclusion holds from connectedness of the web plus
positivity on its edges alone: strictly weaker hypotheses,
so the corollary comes back stronger than the original. -/
theorem eq_const_of_bridge_energy_eq_zero {w : Sym2 V → ℝ} (hG : G.Connected)
    (hw : ∀ u v, G.Adj u v → 0 < w s(u, v)) (f : V → ℝ)
    (hE : ∑ i, f i * laplacianOp (denseWeight G w) f i = 0) :
    ∀ i j, f i = f j := by
  obtain ⟨c, hc⟩ := (bridge_energy_eq_zero_iff G hG hw f).mp hE
  intro i j
  rw [hc i, hc j]


/-! ## Part (b) — the Orthogonal identification

The grid `Fin 21 × Fin 21` with `lap₁ + lap₂` is the box
product of two 21-cycles. The route: adjacency on the cycle is
exactly the two steps `succ`/`pred`; the ordered adjacent-pair
sum over the box product evaluates to twice Orthogonal's step
energy; Part 0's double count turns that into the break
energy of the box product at unit weight.

Technical note: `ManifoldIndex` is a plain `def` for `Fin 21`,
so typeclass search does not see through it; the `Fintype`
instance below is the same device Orthogonal's own module
uses for `GridIndex`. Graph lemmas are applied in term mode
(`cycleGraph_adj'.mp` / `.mpr`, `Fin.val_sub` as a term)
because rewrite matching at implicit transparency cannot see
through the alias either. -/

instance : Fintype ManifoldIndex := by
  show Fintype (Fin 21)
  infer_instance

/-- `succ` is a cycle step: `a` is adjacent to `succ a` on
`cycleGraph 21`. -/
theorem succ_adj_self (a : ManifoldIndex) : (cycleGraph 21).Adj a (succ a) := by
  refine cycleGraph_adj'.mpr (Or.inr ?_)
  have hv := Fin.val_sub (succ a) a
  have hs : (succ a).val = (a.val + 1) % 21 := rfl
  rw [hs] at hv
  have ha := a.isLt
  omega

/-- `pred` is a cycle step: `a` is adjacent to `pred a` on
`cycleGraph 21`. -/
theorem pred_adj_self (a : ManifoldIndex) : (cycleGraph 21).Adj a (pred a) := by
  refine cycleGraph_adj'.mpr (Or.inl ?_)
  have hv := Fin.val_sub a (pred a)
  have hp : (pred a).val = (a.val + 20) % 21 := rfl
  rw [hp] at hv
  have ha := a.isLt
  omega

/-- Adjacency on the 21-cycle is exactly the two steps:
`a'` is adjacent to `a` iff `a' = succ a` or `a' = pred a`. -/
theorem cycle_adj_iff {a a' : ManifoldIndex} :
    (cycleGraph 21).Adj a a' ↔ a' = succ a ∨ a' = pred a := by
  constructor
  · intro h
    have h2 := cycleGraph_adj'.mp h
    rcases h2 with h | h
    · right
      apply Fin.ext
      have hp : (pred a).val = (a.val + 20) % 21 := rfl
      have hv := Fin.val_sub a a'
      rw [hp]
      have ha := a.isLt
      have ha' := a'.isLt
      omega
    · left
      apply Fin.ext
      have hs : (succ a).val = (a.val + 1) % 21 := rfl
      have hv := Fin.val_sub a' a
      rw [hs]
      have ha := a.isLt
      have ha' := a'.isLt
      omega
  · rintro (rfl | rfl)
    · exact succ_adj_self a
    · exact pred_adj_self a

/-- The box product of two 21-cycles is connected — Mathlib's
`Connected.boxProd` at `cycleGraph_connected`. This is the
hypothesis AZ-2W consumes in the demotion below. -/
theorem boxProd_cycle_connected :
    ((cycleGraph 21).boxProd (cycleGraph 21)).Connected :=
  SimpleGraph.Connected.boxProd cycleGraph_connected cycleGraph_connected

/-- The neighbor sum on the 21-cycle: summing over the
neighbors of `a` is summing over its two steps. -/
theorem cycle_adj_sum (a : ManifoldIndex) (h : ManifoldIndex → ℝ) :
    (∑ a' ∈ Finset.univ.filter (fun a' : ManifoldIndex => (cycleGraph 21).Adj a a'),
        h a')
      = h (succ a) + h (pred a) := by
  have hset : Finset.univ.filter (fun a' : ManifoldIndex => (cycleGraph 21).Adj a a')
      = {succ a, pred a} := by
    ext a'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact cycle_adj_iff
  have hne : succ a ≠ pred a := by
    intro hcon
    have hv : (succ a).val = (pred a).val :=
      congrArg (fun x : ManifoldIndex => x.val) hcon
    have hs : (succ a).val = (a.val + 1) % 21 := rfl
    have hp : (pred a).val = (a.val + 20) % 21 := rfl
    rw [hs, hp] at hv
    have ha := a.isLt
    omega
  rw [hset, Finset.sum_pair hne]

/-- The inner evaluation: at a grid point `p`, the ordered
adjacent-pair sum over its box-product neighbors is the sum
of the four squared steps (two directions × two coordinates).
The two box-product adjacency cases are mutually exclusive
(looplessness), so the indicator of the disjunction splits. -/
theorem inner_adj_sum_boxProd (f : GridIndex → ℝ) (p : GridIndex) :
    (∑ q, if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
        then (f q - f p) ^ 2 else 0)
      = (f (succ p.1, p.2) - f p) ^ 2 + (f (pred p.1, p.2) - f p) ^ 2
        + (f (p.1, succ p.2) - f p) ^ 2 + (f (p.1, pred p.2) - f p) ^ 2 := by
  obtain ⟨a, b⟩ := p
  show (∑ q, if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj (a, b) q
        then (f q - f (a, b)) ^ 2 else 0)
      = (f (succ a, b) - f (a, b)) ^ 2 + (f (pred a, b) - f (a, b)) ^ 2
        + (f (a, succ b) - f (a, b)) ^ 2 + (f (a, pred b) - f (a, b)) ^ 2
  have hsplit : ∀ a' b' : ManifoldIndex,
      (if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj (a, b) (a', b')
          then (f (a', b') - f (a, b)) ^ 2 else 0)
      = (if (cycleGraph 21).Adj a a' ∧ b = b'
          then (f (a', b') - f (a, b)) ^ 2 else 0)
        + (if (cycleGraph 21).Adj b b' ∧ a = a'
          then (f (a', b') - f (a, b)) ^ 2 else 0) := by
    intro a' b'
    by_cases h1 : (cycleGraph 21).Adj a a' ∧ b = b' <;>
      by_cases h2 : (cycleGraph 21).Adj b b' ∧ a = a'
    · exfalso
      obtain ⟨h1a, -⟩ := h1
      obtain ⟨-, h2b⟩ := h2
      rw [h2b] at h1a
      exact SimpleGraph.irrefl _ h1a
    · have hAdj : ((cycleGraph 21).boxProd (cycleGraph 21)).Adj (a, b) (a', b') :=
        SimpleGraph.boxProd_adj.mpr (Or.inl h1)
      rw [ite_eq_left hAdj, ite_eq_left h1, ite_eq_right h2, add_zero]
    · have hAdj : ((cycleGraph 21).boxProd (cycleGraph 21)).Adj (a, b) (a', b') :=
        SimpleGraph.boxProd_adj.mpr (Or.inr h2)
      rw [ite_eq_left hAdj, ite_eq_right h1, ite_eq_left h2, zero_add]
    · have hnAdj : ¬ ((cycleGraph 21).boxProd (cycleGraph 21)).Adj (a, b) (a', b') := by
        intro hh
        have h2' := SimpleGraph.boxProd_adj.mp hh
        rcases h2' with hh1 | hh2
        · exact h1 hh1
        · exact h2 hh2
      rw [ite_eq_right hnAdj, ite_eq_right h1, ite_eq_right h2, add_zero]
  have hX : (∑ a', ∑ b', if (cycleGraph 21).Adj a a' ∧ b = b'
        then (f (a', b') - f (a, b)) ^ 2 else 0)
      = (f (succ a, b) - f (a, b)) ^ 2 + (f (pred a, b) - f (a, b)) ^ 2 := by
    have hpoint : ∀ a', (∑ b', if (cycleGraph 21).Adj a a' ∧ b = b'
          then (f (a', b') - f (a, b)) ^ 2 else 0)
        = if (cycleGraph 21).Adj a a' then (f (a', b) - f (a, b)) ^ 2 else 0 := by
      intro a'
      have hif : ∀ b', (if (cycleGraph 21).Adj a a' ∧ b = b'
            then (f (a', b') - f (a, b)) ^ 2 else 0)
          = if b = b' then (if (cycleGraph 21).Adj a a'
              then (f (a', b') - f (a, b)) ^ 2 else 0) else 0 := by
        intro b'
        by_cases hb : b = b' <;> by_cases ha : (cycleGraph 21).Adj a a' <;>
          simp [hb, ha]
      rw [Finset.sum_congr rfl (fun b' _ => hif b'), Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun a' _ => hpoint a'), ← Finset.sum_filter]
    exact cycle_adj_sum a (fun a' => (f (a', b) - f (a, b)) ^ 2)
  have hY : (∑ a', ∑ b', if (cycleGraph 21).Adj b b' ∧ a = a'
        then (f (a', b') - f (a, b)) ^ 2 else 0)
      = (f (a, succ b) - f (a, b)) ^ 2 + (f (a, pred b) - f (a, b)) ^ 2 := by
    rw [Finset.sum_comm]
    have hpoint : ∀ b', (∑ a', if (cycleGraph 21).Adj b b' ∧ a = a'
          then (f (a', b') - f (a, b)) ^ 2 else 0)
        = if (cycleGraph 21).Adj b b' then (f (a, b') - f (a, b)) ^ 2 else 0 := by
      intro b'
      have hif : ∀ a', (if (cycleGraph 21).Adj b b' ∧ a = a'
            then (f (a', b') - f (a, b)) ^ 2 else 0)
          = if a = a' then (if (cycleGraph 21).Adj b b'
              then (f (a', b') - f (a, b)) ^ 2 else 0) else 0 := by
        intro a'
        by_cases ha : a = a' <;> by_cases hb : (cycleGraph 21).Adj b b' <;>
          simp [ha, hb]
      rw [Finset.sum_congr rfl (fun a' _ => hif a'), Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun b' _ => hpoint b'), ← Finset.sum_filter]
    exact cycle_adj_sum b (fun b' => (f (a, b') - f (a, b)) ^ 2)
  have hXY : (∑ a', ∑ b', ((if (cycleGraph 21).Adj a a' ∧ b = b'
            then (f (a', b') - f (a, b)) ^ 2 else 0)
          + (if (cycleGraph 21).Adj b b' ∧ a = a'
            then (f (a', b') - f (a, b)) ^ 2 else 0)))
      = (f (succ a, b) - f (a, b)) ^ 2 + (f (pred a, b) - f (a, b)) ^ 2
          + (f (a, succ b) - f (a, b)) ^ 2 + (f (a, pred b) - f (a, b)) ^ 2 := by
    have e1 : (∑ a', ∑ b', ((if (cycleGraph 21).Adj a a' ∧ b = b'
              then (f (a', b') - f (a, b)) ^ 2 else 0)
            + (if (cycleGraph 21).Adj b b' ∧ a = a'
              then (f (a', b') - f (a, b)) ^ 2 else 0)))
        = ∑ a', ((∑ b', if (cycleGraph 21).Adj a a' ∧ b = b'
              then (f (a', b') - f (a, b)) ^ 2 else 0)
            + (∑ b', if (cycleGraph 21).Adj b b' ∧ a = a'
              then (f (a', b') - f (a, b)) ^ 2 else 0)) :=
      Finset.sum_congr rfl (fun a' _ => Finset.sum_add_distrib)
    have e2 : (∑ a', ((∑ b', if (cycleGraph 21).Adj a a' ∧ b = b'
              then (f (a', b') - f (a, b)) ^ 2 else 0)
            + (∑ b', if (cycleGraph 21).Adj b b' ∧ a = a'
              then (f (a', b') - f (a, b)) ^ 2 else 0)))
        = (∑ a', ∑ b', if (cycleGraph 21).Adj a a' ∧ b = b'
              then (f (a', b') - f (a, b)) ^ 2 else 0)
            + (∑ a', ∑ b', if (cycleGraph 21).Adj b b' ∧ a = a'
              then (f (a', b') - f (a, b)) ^ 2 else 0) :=
      Finset.sum_add_distrib
    rw [e1, e2, hX, hY]
    ring
  calc (∑ q, if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj (a, b) q
          then (f q - f (a, b)) ^ 2 else 0)
      = ∑ a', ∑ b', ((if (cycleGraph 21).Adj a a' ∧ b = b'
            then (f (a', b') - f (a, b)) ^ 2 else 0)
          + (if (cycleGraph 21).Adj b b' ∧ a = a'
            then (f (a', b') - f (a, b)) ^ 2 else 0)) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl (fun a' _ =>
          Finset.sum_congr rfl (fun b' _ => hsplit a' b'))
    _ = (f (succ a, b) - f (a, b)) ^ 2 + (f (pred a, b) - f (a, b)) ^ 2
          + (f (a, succ b) - f (a, b)) ^ 2 + (f (a, pred b) - f (a, b)) ^ 2 :=
        hXY

/-- The predecessor step sum along the first coordinate
equals the successor step sum: reindex by the successor
permutation and use `pred (succ a) = a`. -/
theorem pred_step_sum_fst (f : GridIndex → ℝ) :
    (∑ p, (f (pred p.1, p.2) - f p) ^ 2)
      = ∑ p, (f (succ p.1, p.2) - f p) ^ 2 := by
  rw [← Equiv.sum_comp succEquiv₁
    (fun p : GridIndex => (f (pred p.1, p.2) - f p) ^ 2)]
  apply Finset.sum_congr rfl
  intro p _
  show (f (pred (succ p.1), p.2) - f (succ p.1, p.2)) ^ 2
      = (f (succ p.1, p.2) - f p) ^ 2
  rw [pred_succ, Prod.eta]
  ring

/-- The predecessor step sum along the second coordinate
equals the successor step sum. -/
theorem pred_step_sum_snd (f : GridIndex → ℝ) :
    (∑ p, (f (p.1, pred p.2) - f p) ^ 2)
      = ∑ p, (f (p.1, succ p.2) - f p) ^ 2 := by
  rw [← Equiv.sum_comp succEquiv₂
    (fun p : GridIndex => (f (p.1, pred p.2) - f p) ^ 2)]
  apply Finset.sum_congr rfl
  intro p _
  show (f (p.1, pred (succ p.2)) - f (p.1, succ p.2)) ^ 2
      = (f (p.1, succ p.2) - f p) ^ 2
  rw [pred_succ, Prod.eta]
  ring

/-- The ordered adjacent-pair sum over the box product is
twice Orthogonal's step energy: each grid point contributes
its four squared steps, and the predecessor steps reindex
onto the successor steps. -/
theorem ordered_adj_sum_boxProd (f : GridIndex → ℝ) :
    (∑ p, ∑ q, if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
        then (f q - f p) ^ 2 else 0)
      = 2 * ((∑ p, (f (succ p.1, p.2) - f p) ^ 2)
          + ∑ p, (f (p.1, succ p.2) - f p) ^ 2) := by
  calc (∑ p, ∑ q, if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
          then (f q - f p) ^ 2 else 0)
      = ∑ p, ((f (succ p.1, p.2) - f p) ^ 2 + (f (pred p.1, p.2) - f p) ^ 2
          + (f (p.1, succ p.2) - f p) ^ 2 + (f (p.1, pred p.2) - f p) ^ 2) :=
        Finset.sum_congr rfl (fun p _ => inner_adj_sum_boxProd f p)
    _ = (∑ p, (f (succ p.1, p.2) - f p) ^ 2)
          + (∑ p, (f (pred p.1, p.2) - f p) ^ 2)
          + (∑ p, (f (p.1, succ p.2) - f p) ^ 2)
          + (∑ p, (f (p.1, pred p.2) - f p) ^ 2) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ((∑ p, (f (succ p.1, p.2) - f p) ^ 2)
          + ∑ p, (f (p.1, succ p.2) - f p) ^ 2) := by
        rw [pred_step_sum_fst, pred_step_sum_snd]
        ring

/-- **The identification (b), energy form.** The break
energy of the box product of two 21-cycles at unit weight IS
Orthogonal's step energy — the quantity `lapSum_energy`
writes as `∑ (Δ₁ f)² + ∑ (Δ₂ f)²`. Proof: Part 0's double
count at the box product, with the ordered sum evaluated by
`ordered_adj_sum_boxProd`. -/
theorem breakEnergy_boxProd_cycle_eq (f : GridIndex → ℝ) :
    breakEnergy ((cycleGraph 21).boxProd (cycleGraph 21)) (fun _ => 1) f
      = (∑ p, (f (succ p.1, p.2) - f p) ^ 2)
        + ∑ p, (f (p.1, succ p.2) - f p) ^ 2 := by
  have h := sum_adj_apply_eq_two_mul_sum_edgeFinset
    ((cycleGraph 21).boxProd (cycleGraph 21)) (diffSq f)
  have hpt : ∀ p q : GridIndex,
      (if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
          then diffSq f s(p, q) else 0)
      = (if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
          then (f q - f p) ^ 2 else 0) := by
    intro p q
    by_cases hadj : ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
    · rw [ite_eq_left hadj, ite_eq_left hadj, diffSq_mk]
    · rw [ite_eq_right hadj, ite_eq_right hadj]
  have hcongr : (∑ p, ∑ q,
        if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
          then (f q - f p) ^ 2 else 0)
      = (∑ i, ∑ j, if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj i j
          then (diffSq (V := Fin 21 × Fin 21) f) s(i, j) else 0) :=
    Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => (hpt p q).symm))
  have hG : (∑ p, ∑ q,
        if ((cycleGraph 21).boxProd (cycleGraph 21)).Adj p q
          then (f q - f p) ^ 2 else 0)
      = 2 * ∑ e ∈ ((cycleGraph 21).boxProd (cycleGraph 21)).edgeFinset,
          (diffSq (V := Fin 21 × Fin 21) f) e := hcongr.trans h
  rw [ordered_adj_sum_boxProd] at hG
  have hBE : breakEnergy ((cycleGraph 21).boxProd (cycleGraph 21)) (fun _ => 1) f
      = ∑ e ∈ ((cycleGraph 21).boxProd (cycleGraph 21)).edgeFinset,
          (fun _ => (1 : ℝ)) e * diffSq f e := rfl
  have hE : (∑ e ∈ ((cycleGraph 21).boxProd (cycleGraph 21)).edgeFinset,
        (fun _ => (1 : ℝ)) e * diffSq f e)
      = ∑ e ∈ ((cycleGraph 21).boxProd (cycleGraph 21)).edgeFinset, diffSq f e := by
    apply Finset.sum_congr rfl
    intro e _
    simp
  have hfin : breakEnergy ((cycleGraph 21).boxProd (cycleGraph 21)) (fun _ => 1) f
      = (∑ p, (f (succ p.1, p.2) - f p) ^ 2)
        + ∑ p, (f (p.1, succ p.2) - f p) ^ 2 :=
    mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
      ((congrArg (fun x : ℝ => 2 * x) (hBE.trans hE)).trans hG.symm)
  exact hfin

/-- Orthogonal's grid energy is the master break energy:
`∑ f · (L₁ + L₂) f` at the box product, via `lapSum_energy`
and the identification. -/
theorem lapSum_energy_eq_breakEnergy_boxProd (f : GridIndex → ℝ) :
    (∑ p : GridIndex, f p * (lapSum f) p)
      = breakEnergy ((cycleGraph 21).boxProd (cycleGraph 21)) (fun _ => 1) f := by
  rw [lapSum_energy, breakEnergy_boxProd_cycle_eq]

/-- **The identification (b), kernel form.** `lapSum f = 0`
iff the box product's break energy vanishes. Forward: the
energy identity turns `lapSum f = 0` into step energy zero,
which is the break energy by the identification. Backward:
AZ-2W at the box product (connected, unit weights) makes
`f` constant, and constants are zero modes (`lapSum_const`,
the original O4). -/
theorem lapSum_eq_zero_iff_breakEnergy_boxProd (f : GridIndex → ℝ) :
    lapSum f = 0 ↔ breakEnergy ((cycleGraph 21).boxProd (cycleGraph 21))
      (fun _ => 1) f = 0 := by
  constructor
  · intro h
    have hsum : ∑ p : GridIndex, f p * (lapSum f) p = 0 := by simp [h]
    rw [lapSum_energy, ← breakEnergy_boxProd_cycle_eq] at hsum
    exact hsum
  · intro h
    obtain ⟨c, hc⟩ := (breakEnergy_eq_zero_iff_constant
      ((cycleGraph 21).boxProd (cycleGraph 21)) boxProd_cycle_connected
      (fun u v _ => one_pos) f).mp h
    have hf : f = fun _ => c := funext hc
    rw [hf]
    exact lapSum_const c

/-- **O4+ DEMOTED — the corollary route.** The exact
statement of Orthogonal's `lapSum_eq_zero_iff` (whose name
and seat stand untouched in its own module), reproved here
in a few lines routed entirely through the master theorem:
the kernel identification moves `lapSum f = 0` to vanishing
break energy at the box product, and AZ-2W
(`breakEnergy_eq_zero_iff_constant`, at `Connected.boxProd`
of two cycles, unit weights) closes it. The standalone walk
argument of the original proof is no longer load-bearing. -/
theorem lapSum_eq_zero_iff_via_oneKernel (f : GridIndex → ℝ) :
    lapSum f = 0 ↔ ∃ c, f = fun _ => c := by
  rw [lapSum_eq_zero_iff_breakEnergy_boxProd]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (breakEnergy_eq_zero_iff_constant
      ((cycleGraph 21).boxProd (cycleGraph 21)) boxProd_cycle_connected
      (fun u v _ => one_pos) f).mp h
    exact ⟨c, funext hc⟩
  · rintro ⟨c, rfl⟩
    have hBEc : breakEnergy ((cycleGraph 21).boxProd (cycleGraph 21))
          (fun _ => 1) (fun _ => c)
        = ∑ e ∈ ((cycleGraph 21).boxProd (cycleGraph 21)).edgeFinset,
            diffSq (fun _ => c) e := by
      show (∑ e ∈ ((cycleGraph 21).boxProd (cycleGraph 21)).edgeFinset,
          (fun _ => (1 : ℝ)) e * diffSq (fun _ => c) e) = _
      simp
    refine hBEc.trans ?_
    apply Finset.sum_eq_zero
    intro e _
    induction e using Sym2.inductionOn with
    | hf u v => rw [diffSq_mk]; simp

end ThetLogos
