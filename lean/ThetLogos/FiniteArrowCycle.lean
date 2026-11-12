import Mathlib.Tactic
import ThetLogos.FiniteArrow
import ThetLogos.FiniteArrowEntropy

/-!
# ThetLogos.FiniteArrowCycle — MV-1, the ring-graph exhibit

Queue position 24 (the MV set; spec:
`monotonicity-vortex-equilibrium-scope-2026-11-08.md` §3(b)
+ §4). Band S–M. PRE-REGISTERED DIAL-INELIGIBLE; Dial 2 = 0;
NO CLAIM. Working label only — naming is Zero's.

**The seat.** The Finite Arrow package (FA-1..FA-6, FA-4b)
instantiated at the CYCLE: sites `ZMod n` (`[NeZero n]`),
weights `cycleW n i j = 1` exactly on the two ring
neighbours `j = i ± 1`, else `0`. Everything proved here is
a specialization of a landed general theorem, except the
equilibrium clause (below), which is this seat's own.

**The three roles, kept apart (MV-0 charter).**
- MONOTONES: the Shannon entropy of the evolved field
  never decreases (`cycle_entropyW_monotoneOn`, FA-4b at
  the cycle); the deviation energy never increases
  (`cycle_devEnergy_antitoneOn`, FA-1 at the cycle).
- KEEPER: the total mass is conserved
  (`cycle_sum_arrowFlow`). Conserved, not monotone — it
  refuses to run at all.
- EQUILIBRIUM: the state the run delivers. At the general
  seat FA-2's target is `ker L`, and the general fence
  (K-ARR-EQ) stands untouched: on a DISCONNECTED seat the
  limit is locally constant, not constant. The cycle is
  connected, and here that is proved, not assumed:
  `cycle_laplacianOp_eq_zero_iff` — at this seat
  `laplacianOp (cycleW n) F = 0` iff `F` is constant, the
  forward direction by the adjacency walk (zero energy
  forces equality across every conducting edge
  `i → i + 1`, and the walk reaches every site of
  `ZMod n`). Hence `cycle_arrowFlow_tendsto_const`: the
  flow converges to a constant field.

**Fences.** A finite ring of sites with a heat flow. NOT
the polar vortex, not weather, not a fluid, not the
atmosphere (K-MV-PROXY / K-MV-ATMOS stand armed over any
such telling); the roles are not interchangeable
(K-MV-CONFLATE); nothing here moves a dial (K-MV-DIAL).
The phase-ring seat — the keeper as winding, equilibria
carrying a twist — is MV-2, a different seat and a
different brick.
-/

namespace ThetLogos

/-- **The cycle weights.** `cycleW n i j = 1` iff `j` is a
ring neighbour of `i` (`j = i + 1` or `j = i - 1`) in
`ZMod n`, else `0`. At `n = 2` the two neighbours coincide
and the weight is still `1` (a simple cycle, not a
multigraph); at `n = 1` the single site is its own
neighbour. -/
def cycleW (n : ℕ) : ZMod n → ZMod n → ℝ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- **The cycle weights are a Finite Arrow seat:**
symmetric, nonnegative, with symmetric Laplacian operator
(the third clause by the landed `lapLin_isSymmetric` from
the first). -/
theorem cycleW_props (n : ℕ) [NeZero n] :
    (∀ i j, cycleW n i j = cycleW n j i) ∧ (∀ i j, 0 ≤ cycleW n i j)
      ∧ (lapLin (cycleW n)).IsSymmetric := by
  have hkey : ∀ i j : ZMod n,
      (j = i + 1 ∨ j = i - 1) ↔ (i = j + 1 ∨ i = j - 1) := by
    intro i j
    constructor
    · rintro (h | h)
      · right
        rw [h, add_sub_cancel_right]
      · left
        rw [h, sub_add_cancel]
    · rintro (h | h)
      · right
        rw [h, add_sub_cancel_right]
      · left
        rw [h, sub_add_cancel]
  have hsymm : ∀ i j, cycleW n i j = cycleW n j i := by
    intro i j
    unfold cycleW
    exact if_congr (hkey i j) rfl rfl
  have hnonneg : ∀ i j, 0 ≤ cycleW n i j := by
    intro i j
    unfold cycleW
    split_ifs <;> norm_num
  exact ⟨hsymm, hnonneg, lapLin_isSymmetric _ hsymm⟩

/-- The cycle seat's symmetry witness, named so the
exhibit's statements can carry it (it is the third clause
of `cycleW_props`). -/
def cycleSymm (n : ℕ) [NeZero n] : (lapLin (cycleW n)).IsSymmetric :=
  (cycleW_props n).2.2

/-- **Monotone, at the cycle (FA-4b specialized).** For a
strictly positive initial field, the Shannon entropy of
the evolved field is monotone nondecreasing on `t ≥ 0`. -/
theorem cycle_entropyW_monotoneOn (n : ℕ) [NeZero n] {F : ZMod n → ℝ}
    (hF : ∀ i, 0 < F i) :
    MonotoneOn (fun t => entropyW (arrowFlow (cycleW n) (cycleSymm n) t F))
      (Set.Ici 0) :=
  entropyW_arrowFlow_monotoneOn _ (cycleW_props n).1 (cycleW_props n).2.1
    (cycleSymm n) hF

/-- **Monotone, at the cycle (FA-1 specialized).** The
deviation energy along the flow is antitone on `t ≥ 0`. -/
theorem cycle_devEnergy_antitoneOn (n : ℕ) [NeZero n] (F : ZMod n → ℝ) :
    AntitoneOn (fun t => devEnergy (cycleW n)
      (arrowFlow (cycleW n) (cycleSymm n) t F)) (Set.Ici 0) :=
  devEnergy_arrowFlow_antitoneOn _ (cycleW_props n).1 (cycleW_props n).2.1
    (cycleSymm n) F

/-- **The keeper, at the cycle.** The flow preserves the
total: `∑ j, (θ t) j = ∑ j, θ j` at every time. Conserved —
not monotone, not an equilibrium (MV-0 role charter). -/
theorem cycle_sum_arrowFlow (n : ℕ) [NeZero n] (t : ℝ) (G : ZMod n → ℝ) :
    ∑ j, arrowFlow (cycleW n) (cycleSymm n) t G j = ∑ j, G j :=
  sum_arrowFlow _ (cycleW_props n).1 (cycleSymm n) t G

/-- **Equilibrium at the cycle, characterized (NEW).** For
`[NeZero n]`, `laplacianOp (cycleW n) F = 0` iff `F` is
constant. The forward direction is the connectedness of
the cycle, proved by walking it: zero energy forces
`F i = F (i + 1)` across every conducting edge (the landed
`eq_of_energy_eq_zero`, weight `1` on the edge
`i → i + 1`), induction up the `ℕ`-walk reaches every site
of `ZMod n`. The backward direction is the landed
`laplacianOp_const`. Contrast the general seat, where
`ker L` is the locally constant fields (K-ARR-EQ): the
cycle has one component, so locally constant is constant. -/
theorem cycle_laplacianOp_eq_zero_iff (n : ℕ) [NeZero n] (F : ZMod n → ℝ) :
    laplacianOp (cycleW n) F = 0 ↔ ∃ c, F = fun _ => c := by
  obtain ⟨hw, hw0, -⟩ := cycleW_props n
  constructor
  · intro h
    have hE : ∑ i, F i * laplacianOp (cycleW n) F i = 0 := by
      rw [h]
      simp
    have hstep : ∀ i : ZMod n, F i = F (i + 1) := by
      intro i
      apply eq_of_energy_eq_zero (cycleW n) hw hw0 F hE
      have hwij : cycleW n i (i + 1) = 1 := if_pos (Or.inl rfl)
      rw [hwij]
      exact one_ne_zero
    have hwalk : ∀ k : ℕ, F (k : ZMod n) = F 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by
          push_cast
          ring
        rw [hcast, ← hstep (k : ZMod n), ih]
    refine ⟨F 0, ?_⟩
    funext j
    have hj := hwalk j.val
    rw [ZMod.natCast_zmod_val] at hj
    exact hj
  · rintro ⟨c, rfl⟩
    exact laplacianOp_const _ c

/-- **The equilibrium delivered, at the cycle.** Every
field converges under the flow to a CONSTANT field: FA-2's
`ker L` target, identified as a constant by
`cycle_laplacianOp_eq_zero_iff` (the kernel projection
lies in the kernel — the landed `lapLin_kerProjE`,
transported by `equiv_lapLin`). -/
theorem cycle_arrowFlow_tendsto_const (n : ℕ) [NeZero n] (F : ZMod n → ℝ) :
    ∃ c, Filter.Tendsto (fun t => arrowFlow (cycleW n) (cycleSymm n) t F)
      Filter.atTop (nhds (fun _ => c)) := by
  obtain ⟨hw, hw0, -⟩ := cycleW_props n
  have hker : laplacianOp (cycleW n)
      (kerProj (cycleW n) (cycleSymm n) F) = 0 := by
    show laplacianOp (cycleW n)
      (euclEquiv (kerProjE (cycleW n) (cycleSymm n) (euclEquiv.symm F))) = 0
    rw [← equiv_lapLin, lapLin_kerProjE, map_zero]
  obtain ⟨c, hc⟩ := (cycle_laplacianOp_eq_zero_iff n
    (kerProj (cycleW n) (cycleSymm n) F)).mp hker
  exact ⟨c, hc ▸ arrowFlow_tendsto_kerProj _ hw hw0 (cycleSymm n) F⟩

end ThetLogos
