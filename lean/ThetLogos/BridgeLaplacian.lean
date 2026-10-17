import Mathlib.Tactic

/-!
# ThetLogos.BridgeLaplacian — the bridge exhibit: `L = dᵀ σ d` on a finite
weighted graph (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite weighted-graph algebra**: a finite
  vertex type `V`, a symmetric real weight function `w : V → V → ℝ`
  (nonnegativity is a *hypothesis* on the theorems that need it, never
  baked into the definitions), and the operator algebra of potentials,
  drops, Ohm flows, and divergences on it. Zero sorrys, no new axioms
  (headline theorems checked against the standard three:
  `propext`, `Classical.choice`, `Quot.sound` — see the axiom audit at
  the end of this header).
- THE BRIDGE. The conversation this exhibit answers (Jeff, 2026-10-17,
  “missing bridge I meant”) observed that electric theory pairs two
  different territories — potentials on nodes, currents on edges — and
  that the translator between them is a boundary operator. This file
  makes that literal. Three maps are defined separately and composed:
  the **drop** `dropVec F i j = F j - F i` (the coboundary `d`: a
  node function becomes an antisymmetric edge function), the **Ohm
  factor** `ohm w X i j = w i j * X i j` (the conductance `σ`, the
  material in the middle of the bridge — Ohm's law as a pointwise
  factor), and the **divergence** `diverge X i = ∑ j, X j i` (the return
  crossing `dᵀ`: an edge function is summed back to the nodes). The
  headline theorem `laplacianOp_eq_diverge_ohm_drop` is the
  factorization

      `laplacianOp w F = diverge (ohm w (dropVec F))`,   i.e. `L = dᵀ σ d`,

  where `(laplacianOp w F) i = ∑ j, w i j * (F i - F j)`. The
  factorization is a genuine theorem, not a definitional unfolding: the
  divergence gathers the *transposed* entries `X j i`, so the two sides
  agree only after the symmetry of `w` is spent (`w j i = w i j`).
- SIGN CONVENTION (fixed once, kept throughout): the drop is the
  coboundary orientation `(dF)(i,j) = F j - F i` (rise from `i` to `j`);
  sums of drops around closed paths vanish, which is the Kirchhoff
  voltage law (the sign of “drop” is a convention; `0 = -0`). The
  divergence is the inflow-gathering transpose, chosen so that the
  factorization above produces the standard sign
  `(L F) i = ∑ j, w i j * (F i - F j)`; for the Ohm flow this number is
  the net current leaving node `i`.
- KIRCHHOFF'S LAWS, as theorems here: the **voltage law** is the
  telescoping of drops along a path (`dropVec_telescope`:
  the drops along `i₀ → i₁ → … → iₙ` sum to `F iₙ - F i₀`), with the
  closed-path corollary `dropVec_telescope_closed` (sum `= 0`); the
  **current law** is `sum_laplacianOp_eq_zero`: for symmetric `w` the
  total of `L F` over all nodes vanishes — current is conserved.
- THOMSON / DISSIPATION: `bilin_identity` is the polarized energy
  identity `2 ∑ᵢ Gᵢ (L F)ᵢ = ∑ᵢⱼ w i j (Fᵢ - Fⱼ)(Gᵢ - Gⱼ)` (watch the
  factor of 2 — the symmetrization *is* the proof). Its diagonal is
  `energy_identity`, and `energy_nonneg` is the dissipation statement:
  for `0 ≤ w`, `0 ≤ ∑ᵢ Fᵢ (L F)ᵢ`. `laplacianOp_symm_form` is the
  self-adjointness of `L` as a bilinear form. `energy_eq_zero_iff`
  characterizes the kernel on the support of `w`, with the
  all-positive-weights corollary `eq_const_of_energy_eq_zero` (zero
  energy forces `F` constant) and `laplacianOp_const` (constants are
  equilibria of `Ḟ = -L F`).
- FIEDLER VALUE: `fiedler w` is defined as the `sInf` of the energies
  of mean-zero unit-norm potentials — the variational equilibration
  rate in Rayleigh form. `fiedler_le_energy` is the variational lower
  bound (every admissible `F` has `fiedler w ≤ energy F`) and
  `fiedler_nonneg` gives `0 ≤ fiedler w` for `0 ≤ w`. Edge cases are
  handled honestly, not fudged: if the admissible set is empty (only
  possible for `|V| ≤ 1`, where no mean-zero unit potential exists),
  `sInf ∅ = 0` in `ℝ` and both theorems remain true — the nonneg proof
  case-splits on emptiness for exactly this reason. And
  `fiedlerSet_nonempty_of_exists_ne` discharges the other side: when
  two distinct vertices exist, the admissible set is inhabited — the
  witness is the normalized difference of two vertex deltas,
  `(δ_a - δ_b)/√2`, proved mean-zero and unit-norm — so for `|V| ≥ 2`
  the Fiedler value is the infimum of a genuinely inhabited set.
  (Attainment of the infimum — an eigenvector statement — is not
  claimed; it belongs to the priced exponential-decay follow-on.)
- THE THREE READINGS — AN EQUATION IDENTITY, NOT A CLAIM ABOUT THE
  WORLD. The single operator equation `Ḟ = -L F` is *simultaneously*:
  (i) the equilibration of a resistor network with conductances `w`
  (Ohm's law is the middle factor), (ii) the graph heat / diffusion
  equation with conductivities `w`, and (iii) the continuous-time
  DeGroot consensus dynamics with influence weights `w`. These are
  identifications of *equations* — the same finite algebra read three
  ways. This file claims NOTHING about real circuits, real heat flow,
  or real electorates; a model is not its territory. The consensus /
  conservation content actually proved is algebraic: constants are
  equilibria (`laplacianOp_const`) and the total is conserved
  (`sum_laplacianOp_eq_zero`).
- NOT CLAIMED, PRICED: **Faraday's law** (an EMF around a loop equal to
  a rate of change of flux) is *absent* — it needs cycle/flux data
  (a `2`-chain structure and a flux variable on it) that this
  vertex/edge algebra does not carry; it is the priced second storey.
  **Exponential decay** of `Ḟ = -L F` at rate `fiedler w` (the matrix
  exponential / eigenbasis argument) is priced as the follow-on; what
  stands here is the variational bound itself. Also absent and not
  gestured at: Maxwell theory, continuum limits, spectral
  gap/Poincaré content, and anything Yang–Mills.
- RELATION TO MATHLIB: Mathlib already has a graph Laplacian,
  `SimpleGraph.lapMatrix` (`degMatrix - adjMatrix` for a simple graph,
  unweighted `0/1` adjacency, with positive-semidefiniteness and kernel
  characterizations). This exhibit is not a re-proof of that: it works
  with arbitrary symmetric real **weights** as a function-level
  operator (no matrix, no `SimpleGraph`), and its content is the
  explicit three-map `d / σ / dᵀ` factorization, the Kirchhoff voltage
  telescoping, the polarized energy identity, and the Fiedler
  variational bound, packaged as one exhibit.
- PROVENANCE: Jeff's “missing bridge” of 2026-10-17 (the boundary
  operator as the translator between potentials and flows; Ohm's law
  as the material in the middle of the bridge; Faraday priced as the
  loop-and-flux storey), built under his standing build order. Finite
  toy / background algebra in the shelf sense of `FluxTwist` and
  `SexagesimalClock` — NOT a ladder rung.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The three maps of the bridge

`dropVec` (the coboundary `d`), `ohm` (the conductance factor `σ`),
`diverge` (the return crossing `dᵀ`), and their composite `flowVec`.
The Laplacian `laplacianOp` is defined directly; §2 proves it is the
composite. -/

/-- The drop (coboundary) of a potential `F`: the edge function
`(dF)(i,j) = F j - F i`. -/
def dropVec (F : V → ℝ) (i j : V) : ℝ := F j - F i

/-- Ohm's law as a pointwise factor: multiply an edge function by the
conductance `w`. -/
def ohm (w : V → V → ℝ) (X : V → V → ℝ) (i j : V) : ℝ := w i j * X i j

/-- The Ohm flow of a potential: conductance-weighted drop,
`flowVec w F = ohm w (dropVec F)`. -/
def flowVec (w : V → V → ℝ) (F : V → ℝ) : V → V → ℝ := ohm w (dropVec F)

/-- The divergence (return crossing `dᵀ`): sum an edge function back to
the nodes, gathering the transposed entries. -/
def diverge (X : V → V → ℝ) (i : V) : ℝ := ∑ j, X j i

/-- The weighted graph Laplacian:
`(laplacianOp w F) i = ∑ j, w i j * (F i - F j)`. -/
def laplacianOp (w : V → V → ℝ) (F : V → ℝ) (i : V) : ℝ :=
  ∑ j, w i j * (F i - F j)

theorem dropVec_apply (F : V → ℝ) (i j : V) : dropVec F i j = F j - F i := rfl

theorem dropVec_self (F : V → ℝ) (i : V) : dropVec F i i = 0 := by
  simp [dropVec]

theorem dropVec_antisymm (F : V → ℝ) (i j : V) :
    dropVec F i j = - dropVec F j i := by
  simp only [dropVec]; ring

/-- Linearity of the drop in the potential (additivity). -/
theorem dropVec_add (F G : V → ℝ) (i j : V) :
    dropVec (fun k => F k + G k) i j = dropVec F i j + dropVec G i j := by
  simp only [dropVec]; ring

/-- Linearity of the drop in the potential (scaling). -/
theorem dropVec_smul (c : ℝ) (F : V → ℝ) (i j : V) :
    dropVec (fun k => c * F k) i j = c * dropVec F i j := by
  simp only [dropVec]; ring

/-- Constants have zero drop: every edge of a constant potential is
level. -/
theorem dropVec_const (c : ℝ) (i j : V) : dropVec (fun _ => c) i j = 0 := by
  simp [dropVec]

/-- Kirchhoff voltage law, path form: the drops along a path
`p 0 → p 1 → … → p n` telescope to `F (p n) - F (p 0)`. -/
theorem dropVec_telescope (F : V → ℝ) (p : ℕ → V) (n : ℕ) :
    ∑ k ∈ Finset.range n, dropVec F (p k) (p (k + 1)) = F (p n) - F (p 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [dropVec]
    ring

/-- Kirchhoff voltage law, closed-path form: the drops around any
closed path sum to zero. -/
theorem dropVec_telescope_closed (F : V → ℝ) (p : ℕ → V) (n : ℕ)
    (h : p n = p 0) :
    ∑ k ∈ Finset.range n, dropVec F (p k) (p (k + 1)) = 0 := by
  rw [dropVec_telescope, h, sub_self]

theorem ohm_apply (w X : V → V → ℝ) (i j : V) :
    ohm w X i j = w i j * X i j := rfl

theorem flowVec_apply (w : V → V → ℝ) (F : V → ℝ) (i j : V) :
    flowVec w F i j = w i j * (F j - F i) := rfl

/-- The Ohm flow is antisymmetric (for symmetric conductance): the
current into `i` from `j` is minus the current into `j` from `i`. -/
theorem flowVec_antisymm (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) (F : V → ℝ)
    (i j : V) :
    flowVec w F i j = - flowVec w F j i := by
  simp only [flowVec_apply]
  rw [hw j i]; ring

theorem diverge_apply (X : V → V → ℝ) (i : V) :
    diverge X i = ∑ j, X j i := rfl

theorem laplacianOp_apply (w : V → V → ℝ) (F : V → ℝ) (i : V) :
    laplacianOp w F i = ∑ j, w i j * (F i - F j) := rfl

/-! ## §2. The factorization `L = dᵀ σ d`, and the current law -/

/-- **The bridge factorization.** The Laplacian is the composite of the
three separately defined maps: drop (`d`), Ohm factor (`σ`), divergence
(`dᵀ`). A genuine theorem, not `rfl`: the divergence gathers transposed
entries `X j i`, so the identification spends the symmetry of `w`. -/
theorem laplacianOp_eq_diverge_ohm_drop (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F : V → ℝ) :
    laplacianOp w F = diverge (ohm w (dropVec F)) := by
  funext i
  simp only [laplacianOp_apply, diverge_apply, ohm_apply, dropVec_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hw j i]

/-- The factorization with the Ohm flow named: `L F = dᵀ (flow of F)`. -/
theorem laplacianOp_eq_diverge_flow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F : V → ℝ) :
    laplacianOp w F = diverge (flowVec w F) :=
  laplacianOp_eq_diverge_ohm_drop w hw F

/-- Kirchhoff current law: for symmetric `w`, the total current over
all nodes vanishes — what leaves somewhere arrives somewhere. Read in
the consensus dynamics, this is conservation of the total (hence of
the mean). -/
theorem sum_laplacianOp_eq_zero (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F : V → ℝ) :
    ∑ i, laplacianOp w F i = 0 := by
  have hT : (∑ i, ∑ j, w j i * (F j - F i)) = ∑ i, ∑ j, w i j * (F i - F j) :=
    Finset.sum_comm
  have h0 : (∑ i, ∑ j, w i j * (F i - F j))
      + (∑ i, ∑ j, w j i * (F j - F i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [hw j i]; ring
  rw [hT] at h0
  have hS : (∑ i, laplacianOp w F i) = ∑ i, ∑ j, w i j * (F i - F j) := rfl
  rw [hS]
  linarith

/-! ## §3. Energy, dissipation, self-adjointness (Thomson) -/

/-- The polarized energy identity: twice the bilinear pairing is the
conductance-weighted sum of products of drops. The symmetrization in
the proof is the content; the factor of `2` is real. -/
theorem bilin_identity (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F G : V → ℝ) :
    2 * (∑ i, G i * laplacianOp w F i)
      = ∑ i, ∑ j, w i j * (F i - F j) * (G i - G j) := by
  have hA : (∑ i, G i * laplacianOp w F i)
      = ∑ i, ∑ j, G i * (w i j * (F i - F j)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [laplacianOp_apply, Finset.mul_sum]
  have hB : (∑ i, ∑ j, G j * (w j i * (F j - F i)))
      = ∑ i, ∑ j, G i * (w i j * (F i - F j)) := Finset.sum_comm
  have hS : (∑ i, ∑ j, w i j * (F i - F j) * (G i - G j))
      = (∑ i, ∑ j, G i * (w i j * (F i - F j)))
        + ∑ i, ∑ j, G j * (w j i * (F j - F i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]; ring
  rw [hS, hB, ← hA]
  ring

/-- The energy identity (diagonal of `bilin_identity`): twice the
quadratic form is the conductance-weighted sum of squared drops. -/
theorem energy_identity (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F : V → ℝ) :
    2 * (∑ i, F i * laplacianOp w F i)
      = ∑ i, ∑ j, w i j * (F i - F j) ^ 2 := by
  have h := bilin_identity w hw F F
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The energy identity in half form. -/
theorem energy_eq_half (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F : V → ℝ) :
    (∑ i, F i * laplacianOp w F i)
      = (1 / 2) * ∑ i, ∑ j, w i j * (F i - F j) ^ 2 := by
  have h := energy_identity w hw F
  linarith

/-- Dissipation is nonnegative (Thomson): for nonneg symmetric
conductances, the quadratic form of `L` is nonnegative. -/
theorem energy_nonneg (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (F : V → ℝ) :
    0 ≤ ∑ i, F i * laplacianOp w F i := by
  rw [energy_eq_half w hw F]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw0 i j) (sq_nonneg _)

/-- Self-adjointness of `L` as a bilinear form. -/
theorem laplacianOp_symm_form (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (F G : V → ℝ) :
    (∑ i, G i * laplacianOp w F i) = ∑ i, F i * laplacianOp w G i := by
  have h1 := bilin_identity w hw F G
  have h2 := bilin_identity w hw G F
  have hS : (∑ i, ∑ j, w i j * (F i - F j) * (G i - G j))
      = ∑ i, ∑ j, w i j * (G i - G j) * (F i - F j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hS] at h1
  linarith

/-! ## §4. The kernel -/

/-- Zero energy iff every conductance-weighted squared drop vanishes:
`F` is constant on the support of `w` (made precise in the lemmas
below). -/
theorem energy_eq_zero_iff (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (F : V → ℝ) :
    (∑ i, F i * laplacianOp w F i = 0)
      ↔ ∀ i j, w i j * (F i - F j) ^ 2 = 0 := by
  have hE := energy_identity w hw F
  constructor
  · intro h
    have hS : (∑ i, ∑ j, w i j * (F i - F j) ^ 2) = 0 := by linarith
    have hrow : ∀ i, (∑ j, w i j * (F i - F j) ^ 2) = 0 := by
      have hiff := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg
          fun j _ => mul_nonneg (hw0 i j) (sq_nonneg _))).mp hS
      exact fun i => hiff i (Finset.mem_univ i)
    intro i j
    have hiff := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw0 i j) (sq_nonneg _))).mp (hrow i)
    exact hiff j (Finset.mem_univ j)
  · intro h
    have hS : (∑ i, ∑ j, w i j * (F i - F j) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      exact h i j
    linarith

/-- Zero energy forces `F i = F j` across every conducting edge. -/
theorem eq_of_energy_eq_zero (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (F : V → ℝ)
    (hE : ∑ i, F i * laplacianOp w F i = 0)
    {i j : V} (hij : w i j ≠ 0) : F i = F j := by
  have h := (energy_eq_zero_iff w hw hw0 F).mp hE i j
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 hij
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)

/-- With all off-diagonal conductances positive, zero energy iff `F`
is constant (the forward, content-bearing direction). -/
theorem eq_const_of_energy_eq_zero (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hpos : ∀ i j, i ≠ j → 0 < w i j)
    (F : V → ℝ)
    (hE : ∑ i, F i * laplacianOp w F i = 0) : ∀ i j, F i = F j := by
  intro i j
  by_cases h : i = j
  · rw [h]
  · exact eq_of_energy_eq_zero w hw hw0 F hE (ne_of_gt (hpos i j h))

/-- Constants are equilibria of `Ḟ = -L F`: the Laplacian kills every
constant potential. (No symmetry or nonnegativity needed.) -/
theorem laplacianOp_const (w : V → V → ℝ) (c : ℝ) :
    laplacianOp w (fun _ => c) = 0 := by
  funext i
  simp [laplacianOp]

/-! ## §5. The Fiedler value (variational equilibration rate) -/

/-- The admissible energies: energies of mean-zero, unit-norm
potentials. (Empty when `|V| ≤ 1` — see the header; `fiedler` handles
that case honestly.) -/
def fiedlerSet (w : V → V → ℝ) : Set ℝ :=
  {x | ∃ F : V → ℝ, (∑ i, F i = 0) ∧ (∑ i, F i ^ 2 = 1)
    ∧ x = ∑ i, F i * laplacianOp w F i}

/-- The Fiedler value: the variational lower bound of the energy on
mean-zero unit potentials — the Rayleigh-form equilibration rate of
`Ḟ = -L F`. -/
noncomputable def fiedler (w : V → V → ℝ) : ℝ := sInf (fiedlerSet w)

theorem fiedler_def (w : V → V → ℝ) : fiedler w = sInf (fiedlerSet w) := rfl

/-- The variational bound: every mean-zero unit potential has energy
at least `fiedler w`. -/
theorem fiedler_le_energy (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (F : V → ℝ)
    (hF0 : ∑ i, F i = 0) (hF1 : ∑ i, F i ^ 2 = 1) :
    fiedler w ≤ ∑ i, F i * laplacianOp w F i := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨G, -, -, rfl⟩
    exact energy_nonneg w hw hw0 G
  · exact ⟨F, hF0, hF1, rfl⟩

/-- The admissible set is nonempty whenever two distinct vertices
exist: the normalized difference of the two vertex deltas,
`F = (δ_a - δ_b) / √2`, is mean-zero and unit-norm. So for `|V| ≥ 2`
the Fiedler value is the infimum of a genuinely inhabited set. -/
theorem fiedlerSet_nonempty_of_exists_ne (w : V → V → ℝ) {a b : V}
    (hab : a ≠ b) : (fiedlerSet w).Nonempty := by
  classical
  set c : ℝ := (Real.sqrt 2)⁻¹ with hc
  set G : V → ℝ := fun i => if i = a then 1 else if i = b then -1 else 0 with hG
  have hGa : G a = 1 := if_pos rfl
  have hGb : G b = -1 := by simp [hG, Ne.symm hab]
  have hG0 : ∀ i : V, i ∉ ({a, b} : Finset V) → G i = 0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp only [hG]
    rw [if_neg hi.1, if_neg hi.2]
  have hsumG : ∑ i, G i = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset V))
      (fun i _ hi => hG0 i hi), Finset.sum_pair hab, hGa, hGb]
    norm_num
  have hsumG2 : ∑ i, G i ^ 2 = 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset V))
      (fun i _ hi => by rw [hG0 i hi]; norm_num), Finset.sum_pair hab, hGa, hGb]
    norm_num
  have hc2 : c ^ 2 = 1 / 2 := by
    rw [hc, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  refine ⟨∑ i, (c * G i) * laplacianOp w (fun k => c * G k) i,
    (fun k => c * G k), ?_, ?_, rfl⟩
  · rw [← Finset.mul_sum, hsumG, mul_zero]
  · have : ∀ i : V, (c * G i) ^ 2 = c ^ 2 * (G i ^ 2) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.mul_sum, hsumG2, hc2]
    norm_num

/-- The Fiedler value is nonnegative for nonneg conductances. The
proof case-splits on emptiness of the admissible set: if it is empty,
`sInf ∅ = 0` in `ℝ` and there is nothing to bound. -/
theorem fiedler_nonneg (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) : 0 ≤ fiedler w := by
  by_cases h : (fiedlerSet w).Nonempty
  · apply le_csInf h
    rintro x ⟨G, -, -, rfl⟩
    exact energy_nonneg w hw hw0 G
  · have hempty : fiedlerSet w = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [fiedler_def, hempty, Real.sInf_empty]

end ThetLogos
