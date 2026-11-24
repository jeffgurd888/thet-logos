import Mathlib.Tactic
import ThetLogos.IdensityDefinition
import ThetLogos.ModularTime
import ThetLogos.RefractiveThermalEntropyPin

/-!
# ThetLogos.IdensityFlowPin — the TF line: Idensity's
# temporal / flow-based faces, tested as theorems

**Lane-grade pin, built 2026-11-22 on Zero's fire word
"Fire the full TF line" (2026-11-22 10:15 EST), on the
IdensityDefinition tip `f869fdc`. NO CLAIM. Pre-registered
DIAL-INELIGIBLE; dials 0/4 under every outcome.**

Commission: Zero's reversal of ID-3 Ruling 3 (2026-11-22
02:57 EST, verbatim: "go back yes temporal and flow
based") restored the FULL reading of "invariant" in
Idensity's definition — relabeling, temporal, AND
flow-based — and his "scope it" commissioned the scope of
record: `idensity-temporal-flow-scope-2026-11-22.md`.
That scope's audit is this module's foundation, and its
load-bearing observation is the hinge of every brick
below: **`idensity` depends on the ambient weight `w`
ONLY through the marginal `margWeightSet w s.1`, and on
the adjacency only through `boundaryCard a s.1`.** Every
invariance question for Idensity is therefore exactly an
invariance question for a marginal under a transformation
of `w` — no more, no less.

The banked module (`ThetLogos.IdensityDefinition`) is NOT
edited: its face already states the full reading, with the
temporal and flow-based faces as the definition's
MEANING, not theorems. This module supplies the first
theorems those faces can honestly carry — and the kill
that fences the reading they cannot.

**Bricks (scope §7 sequencing):** TF-0 the factoring
lemma → TF-1 own-flow stationarity at the region seat →
TF-3 the temporal reading of the numerator → TF-2a
ambient transport and the conditional invariance forms →
TF-2b the kill exhibit, banking last in its pair so the
surviving forms are already on record when it fires.

**Kills registry (scope §4):** K-IDENSITY-FLOW
(pre-registered, TF-2b, EXPECTED TO FIRE — blanket
invariance under ambient step dynamics is false),
K-IDENSITY-FLOW-RESTATE (armed on TF-1). Standing, on
every brick: K-IDENSITY-PROXY (no bulk denominator),
K-IDENSITY-DIAL (no dial movement in either direction of
presentation; Dial 2 = 0), K-IDENSITY-DOUBLE (at the
own-modular seat the pair is (x, x) — the conservation
below is of the ONE number read twice, never of two
conserved quantities), K-IDENSITY-IMPORT (no continuum
modular theory: no Tomita–Takesaki beyond the finite
matrix seat already in census, no type-III language, no
JLMS-style identifications), K-IDENSITY-LAUNDER (nothing
here is a gravity object, a response law, or evidence
about gravity), K-TRID-RESTATE (cited, never re-proved),
K-TRID-BREAK (a flow ON the seat is not the ternary's
breaking, and no header may say so).

**FRONTIER, flagged never priced (scope §5):** continuum
Tomita–Takesaki invariance; quantum (non-diagonal)
ambient flows at the region seat (no region modular
operator exists); a data-processing law for
`regionEntropy`; "invariant state information" as a
distinct observable (absent — TF-3's face statement is
the whole truth on this point).
-/

namespace ThetLogos

/-! ## Brick TF-0 — the factoring lemma

The hinge, proved: `idensity` factors through the
marginal. If a transformation of the ambient weight fixes
the marginal at the region, it fixes the pair — both
components, at once, for every flow. And the transport
split: the denominator involves neither the weight, the
reference energies, nor `β`, so under ANY transformation
of the weight alone, all motion of the pair is numerator
motion. -/

section Factoring

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- The information component factors through the
    marginal (Tier T1 — proved): equal marginals at the
    region give equal region entropies, by `regionEntropy`'s
    definition (H-1). -/
theorem regionEntropy_eq_of_marg_eq (w w' : (∀ i, X i) → ℝ)
    (s : Finset κ) (h : margWeightSet w s = margWeightSet w' s) :
    regionEntropy w s = regionEntropy w' s := by
  unfold regionEntropy
  rw [h]

/-- The modular-energy component factors through the
    marginal (Tier T1 — proved): `regionRefModularEnergy`
    is the marginal expectation of the reference modular
    eigenvalues (`margExpect`, ID-4a), so equal marginals
    give equal values. -/
theorem regionRefModularEnergy_eq_of_marg_eq
    (w w' : (∀ i, X i) → ℝ) (s : Finset κ)
    (E : (∀ i : s, X i) → ℝ) (β : ℝ)
    (h : margWeightSet w s = margWeightSet w' s) :
    regionRefModularEnergy w s E β
      = regionRefModularEnergy w' s E β := by
  unfold regionRefModularEnergy margExpect
  rw [h]

/-- **The factoring lemma** (Tier T1 — proved): if two
    ambient weights have the same marginal at the region,
    their Idensity pairs at that region are equal — for
    every adjacency, every reference energy function, and
    every `β`. Every invariance statement in this module
    is discharged through this one lemma: a transformation
    of `w` that fixes the marginal fixes the pair. -/
theorem idensity_eq_of_marg_eq (a : κ → κ → ℝ)
    (w w' : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ)
    (h : margWeightSet w s.1 = margWeightSet w' s.1) :
    idensity a w s E β = idensity a w' s E β := by
  unfold idensity
  rw [regionEntropy_eq_of_marg_eq w w' s.1 h,
    regionRefModularEnergy_eq_of_marg_eq w w' s.1 E β h]

/-- **The denominator split** (Tier T1 — proved): each
    component of the pair, times the boundary card, is
    exactly its numerator — the denominator
    `boundaryCard a s.1` involves neither `w`, nor `E`,
    nor `β`. Under any transformation of the weight alone,
    the denominator stands and all motion of the pair is
    numerator motion. This is the transport split TF-2
    consumes. -/
theorem idensity_denom_invariant (a : κ → κ → ℝ)
    (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ) :
    (idensity a w s E β).1 * (boundaryCard a s.1 : ℝ)
        = regionEntropy w s.1
      ∧ (idensity a w s E β).2 * (boundaryCard a s.1 : ℝ)
        = regionRefModularEnergy w s.1 E β := by
  have hc : (boundaryCard a s.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr s.2
  constructor
  · rw [idensity_fst]
    exact div_mul_cancel₀ _ hc
  · rw [idensity_snd]
    exact div_mul_cancel₀ _ hc

end Factoring

/-! ## Brick TF-1 — own-flow stationarity at the region seat

The one seat where a genuine temporal theorem already has
all its ingredients in census: at the own-modular seat the
marginal is a Gibbs weight, and Gibbs weights are the
corpus's proved stationary objects.

**Priced friction, on the face (scope §3 TF-1):** the
cited flow theorems (`ModularTime.diagFlow`) are stated
over `Fin N`; the region configuration type is a general
Fintype. This brick takes route (i): the diagonal-flow
triviality lemma is RESTATED over a general Fintype index
(its proof is entrywise, mirrored from
`diagFlow_trivial_of_commute`), and the flow is given an
action on WEIGHTS — the audit's absence #1 (no flow acted
on a classical weight anywhere in either tree) is built
here: evolve the diagonal state by the flow, read the
diagonal back as a weight.

**The honest thinness, on the face:** conjugation by a
diagonal unitary fixes every diagonal state, so the
weight-level flow is the identity on weights — the region
seat's content is exactly that the Gibbs marginal, as a
diagonal state, is fixed by its own flow, and TF-0 then
fixes the pair. **K-IDENSITY-FLOW-RESTATE assessment:**
the brick does NOT collapse to pure citation + TF-0 — it
carries a genuinely re-proved general-index lemma and new
flow-on-weights vocabulary that existed nowhere in-tree —
so it banks as a theorem brick; its thinness is disclosed
here, not hidden. -/

section DiagonalFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The diagonal flow over a general Fintype index**
    (Tier T2 — definition): `ModularTime.diagFlow`'s form
    with `Fin N` replaced by an arbitrary finite index —
    conjugation of a matrix by the diagonal modular
    unitaries of the weight `w`, σ_s(a) = ρ^{is} a ρ^{−is}
    for ρ = diag(w). -/
noncomputable def diagFlowι (w : ι → ℝ) (s : ℝ)
    (a : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun j => cpowI (w j) s) * a
    * Matrix.diagonal (fun j => cpowI (w j) (-s))

/-- **Diagonal-flow triviality, general index** (Tier T1
    — proved): an observable commuting with the diagonal
    generator is flow-fixed, at any finite index. The
    entrywise proof of `ModularTime.diagFlow_trivial_of_
    commute` (the `Fin N` form, in census), restated —
    where two weights coincide the modular phases cancel;
    where they differ, the commutator forces the entry to
    vanish. -/
theorem diagFlowι_trivial_of_commute (w : ι → ℝ) (s : ℝ)
    (a : Matrix ι ι ℂ)
    (hcomm : Matrix.diagonal (fun j => (w j : ℂ)) * a
      = a * Matrix.diagonal (fun j => (w j : ℂ))) :
    diagFlowι w s a = a := by
  have hentry : ∀ i j, (diagFlowι w s a) i j
      = cpowI (w i) s * a i j * cpowI (w j) (-s) := by
    intro i j
    unfold diagFlowι
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hcomm_ij : ∀ i j, (w i : ℂ) * a i j
      = a i j * (w j : ℂ) := by
    intro i j
    have h3 := congrArg (fun M : Matrix ι ι ℂ => M i j) hcomm
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h3
    exact h3
  ext i j
  rw [hentry i j]
  by_cases hwij : w i = w j
  · -- Equal weights: the modular phases cancel.
    have hphase : cpowI (w i) s * cpowI (w j) (-s) = 1 := by
      unfold cpowI
      rw [← Complex.exp_add]
      have hexp : Complex.I * (s : ℂ) * (Real.log (w i) : ℂ)
          + Complex.I * (((-s : ℝ) : ℂ)) * (Real.log (w j) : ℂ)
          = 0 := by
        have hcast : (((-s : ℝ) : ℂ)) = -((s : ℝ) : ℂ) := by
          push_cast; ring
        rw [hcast, hwij]
        ring
      rw [hexp, Complex.exp_zero]
    calc cpowI (w i) s * a i j * cpowI (w j) (-s)
        = (cpowI (w i) s * cpowI (w j) (-s)) * a i j := by ring
      _ = a i j := by rw [hphase, one_mul]
  · -- Distinct weights: the commutator forces the entry
    -- to vanish.
    have haij : a i j = 0 := by
      have hne : (w i : ℂ) ≠ (w j : ℂ) := by
        intro hcon
        apply hwij
        exact_mod_cast hcon
      have hsub : ((w i : ℂ) - (w j : ℂ)) * a i j = 0 := by
        linear_combination hcomm_ij i j
      exact (mul_eq_zero.mp hsub).resolve_left
        (sub_ne_zero.mpr hne)
    rw [haij]
    simp

/-- **The flow's action on weights** (Tier T2 —
    definition): the diagonal state of the weight `p`,
    evolved for time `t` under the diagonal flow generated
    by `g`, read back along the diagonal as a weight. The
    audit's absence #1 — no flow acted on a classical
    weight anywhere in either tree — is built here, at the
    only seat the tree can carry: the diagonal seat. -/
noncomputable def flowWeight (g p : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun z => (diagFlowι g t
    (Matrix.diagonal (fun j => (p j : ℂ))) z z).re

/-- **Weights are flow-fixed at the diagonal seat**
    (Tier T1 — proved): a diagonal state commutes with
    every diagonal generator, so its own flow — and any
    diagonal flow — fixes it, for all real times. This is
    the finite seat's genuine stationarity content, stated
    at the weight level where Idensity consumes it. -/
theorem flowWeight_fixed (g p : ι → ℝ) (t : ℝ) :
    flowWeight g p t = p := by
  have hcomm : Matrix.diagonal (fun j => (g j : ℂ))
        * Matrix.diagonal (fun j => (p j : ℂ))
      = Matrix.diagonal (fun j => (p j : ℂ))
        * Matrix.diagonal (fun j => (g j : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun j => ?_)
    show (g j : ℂ) * (p j : ℂ) = (p j : ℂ) * (g j : ℂ)
    exact mul_comm _ _
  funext z
  show (diagFlowι g t
    (Matrix.diagonal (fun j => (p j : ℂ))) z z).re = p z
  rw [diagFlowι_trivial_of_commute g t _ hcomm]
  simp

end DiagonalFlow

section OwnSeatFlow

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- **The own-modular marginal is flow-fixed** (Tier T1 —
    proved): at the own-modular seat, the region's own
    modular flow — the flow generated by the Gibbs weight
    of the reference energies — fixes the marginal, for
    all real times. -/
theorem margWeightSet_ownSeat_flow_fixed
    (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (E : (∀ i : s, X i) → ℝ) (β : ℝ) (t : ℝ)
    (hw : margWeightSet w s
      = ModularVariance.gibbsProb E β) :
    flowWeight (ModularVariance.gibbsProb E β)
        (margWeightSet w s) t
      = margWeightSet w s := by
  rw [flowWeight_fixed]

/-- **Own-flow stationarity of Idensity** (Tier T1 —
    proved): at the own-modular seat, the Idensity pair is
    invariant under the region's own modular flow — any
    ambient weight whose marginal is the flow-evolved
    marginal carries the same pair, for all real times,
    via TF-0: the flow fixes the (Gibbs) marginal,
    therefore fixes both components. **This is the full
    reading's first TEMPORAL theorem, at exactly one
    seat** — the own-modular seat, under its own flow. It
    says nothing about an ambient or foreign flow: that is
    TF-2's ground, and the blanket form dies there
    (K-IDENSITY-FLOW). **K-IDENSITY-DOUBLE on the face:**
    at this seat the pair is (x, x); what is conserved is
    the one number read twice. -/
theorem idensity_ownSeat_flow_invariant (a : κ → κ → ℝ)
    (w w' : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β t : ℝ)
    (hw : margWeightSet w s.1
      = ModularVariance.gibbsProb E β)
    (hw' : margWeightSet w' s.1
      = flowWeight (ModularVariance.gibbsProb E β)
          (margWeightSet w s.1) t) :
    idensity a w' s E β = idensity a w s E β := by
  apply idensity_eq_of_marg_eq
  rw [hw', flowWeight_fixed]

end OwnSeatFlow

/-! ## Brick TF-3 — the temporal reading of the numerator

The audit's finding, cashed: the numerator's first
component, "invariant state information," has exactly
ONE temporal referent in-tree — the entropy of a weight
that is stationary under its own flow. **Face statement
(no theorem claimed):** no in-tree quantity distinct from
`entropyW` / `regionEntropy` answers to "invariant state
information"; the temporal reading of Zero's numerator IS
entropy-of-a-stationary-weight. Anything richer is an
absence (scope §5), not a definition this line may
invent. **Overlap disclosed at full rank:** this brick
neighbours the tridentity scope's Brick F2 (the
"invariant state" predicate over `gibbsWeight_stationary`
/ `gibbs_kms_flux_stationary`), which was Zero-gated
there and never built; TF-3 does NOT build F2's
predicate — it proves the region-seat conservation
corollary under THIS commission. -/

section OwnSeatTemporal

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- **Region entropy is conserved under diagonal flow**
    (Tier T1 — proved): the entropy of the flow-evolved
    marginal is the region entropy, for every diagonal
    generator and all real times — the numerator's first
    component, read temporally, at the diagonal seat. -/
theorem regionEntropy_flowWeight_eq
    (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (g : (∀ i : s, X i) → ℝ) (t : ℝ) :
    entropyW (flowWeight g (margWeightSet w s) t)
      = regionEntropy w s := by
  rw [flowWeight_fixed]
  rfl

/-- **The numerator's temporal reading, at the own seat**
    (Tier T1 — proved): at the own-modular seat, the
    region entropy of the own-flow-evolved marginal is
    the region entropy — "invariant state information,"
    cashed as the one conservation the tree carries. -/
theorem regionEntropy_ownSeat_conserved
    (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (E : (∀ i : s, X i) → ℝ) (β : ℝ) (t : ℝ)
    (hw : margWeightSet w s
      = ModularVariance.gibbsProb E β) :
    entropyW (flowWeight (ModularVariance.gibbsProb E β)
        (margWeightSet w s) t)
      = regionEntropy w s :=
  regionEntropy_flowWeight_eq w s _ t

/-- **The pair's first component is conserved at the own
    seat** (Tier T1 — proved): the (x, x) corollary of
    TF-1 read on component 1 alone — under the region's
    own modular flow, the information component of the
    pair does not move. -/
theorem idensity_fst_ownSeat_conserved (a : κ → κ → ℝ)
    (w w' : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β t : ℝ)
    (hw : margWeightSet w s.1
      = ModularVariance.gibbsProb E β)
    (hw' : margWeightSet w' s.1
      = flowWeight (ModularVariance.gibbsProb E β)
          (margWeightSet w s.1) t) :
    (idensity a w' s E β).1 = (idensity a w s E β).1 :=
  congrArg Prod.fst
    (idensity_ownSeat_flow_invariant a w w' s E β t hw hw')

end OwnSeatTemporal

/-! ## Brick TF-2a — ambient transport, conditional form

The audit's absence #2 — no definition transported
`margWeightSet` under a kernel — is built here: the
pushforward of an ambient weight under a step kernel, in
the row convention of `ThermalExpansionPin.kernelIter`
and `RefractiveThermalEntropyPin.IsStationary`
(`(μP) j = ∑ i, μ i * P i j`). Against that vocabulary:
the transport law's fixed half (the denominator stands),
and the conditional invariance forms — invariance holds
exactly when the dynamics preserves the marginal, with
stationarity of the marginal as the named sufficient
case. -/

section PushWeight

variable {ι : Type*} [Fintype ι]

/-- **The pushed weight** (Tier T2 — definition): one
    ambient step of the weight `w` under the kernel `P`,
    `(wP) x = ∑ y, w y * P y x` — the pushforward the
    audit found absent, in the tree's standing row
    convention. -/
noncomputable def pushWeight (P : ι → ι → ℝ) (w : ι → ℝ) :
    ι → ℝ :=
  fun x => ∑ y, w y * P y x

/-- The pushed weight, unfolded. -/
theorem pushWeight_apply (P : ι → ι → ℝ) (w : ι → ℝ)
    (x : ι) :
    pushWeight P w x = ∑ y, w y * P y x :=
  rfl

/-- **Stationarity is pushforward-fixedness** (Tier T1 —
    proved): a weight stationary for a kernel in
    `IsStationary`'s shape is exactly a fixed point of
    the pushforward. -/
theorem pushWeight_eq_of_isStationary (P : ι → ι → ℝ)
    (π : ι → ℝ) (h : IsStationary P π) :
    pushWeight P π = π :=
  funext fun j => h j

end PushWeight

section AmbientTransport

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- **The transport law's fixed half** (Tier T1 —
    proved): after one ambient step, the pair's
    denominator is still `boundaryCard a s.1` — the push
    moves the numerators only (TF-0's split, applied at
    the pushed weight). -/
theorem idensity_push_denom (a : κ → κ → ℝ)
    (P : (∀ i, X i) → (∀ i, X i) → ℝ) (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ) :
    (idensity a (pushWeight P w) s E β).1
        * (boundaryCard a s.1 : ℝ)
        = regionEntropy (pushWeight P w) s.1
      ∧ (idensity a (pushWeight P w) s E β).2
          * (boundaryCard a s.1 : ℝ)
        = regionRefModularEnergy (pushWeight P w) s.1 E β :=
  idensity_denom_invariant a (pushWeight P w) s E β

/-- **Conditional invariance, marginal form** (Tier T1 —
    proved): if one ambient step preserves the marginal
    at the region, the pair is invariant under that step
    — via TF-0. This is the exact sufficient condition
    for flow invariance of Idensity, usable by every
    later dynamics pin. -/
theorem idensity_invariant_of_marg_preserved
    (a : κ → κ → ℝ)
    (P : (∀ i, X i) → (∀ i, X i) → ℝ) (w : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ)
    (h : margWeightSet (pushWeight P w) s.1
      = margWeightSet w s.1) :
    idensity a (pushWeight P w) s E β
      = idensity a w s E β :=
  idensity_eq_of_marg_eq a (pushWeight P w) w s E β h

/-- **Conditional invariance, stationary form** (Tier
    T1 — proved): the named special case — if the
    marginal is stationary for the region-read dynamics
    (in `IsStationary`'s shape), then any ambient weight
    whose marginal is the pushed marginal carries the
    same pair. Stationarity of the marginal is
    sufficient; TF-2b shows some such condition is
    necessary, by killing the blanket form. -/
theorem idensity_invariant_of_stationary_marg
    (a : κ → κ → ℝ) (w w' : (∀ i, X i) → ℝ)
    (s : {s : Finset κ // boundaryCard a s ≠ 0})
    (Q : (∀ i : s.1, X i) → (∀ i : s.1, X i) → ℝ)
    (E : (∀ i : s.1, X i) → ℝ) (β : ℝ)
    (hQ : IsStationary Q (margWeightSet w s.1))
    (hw' : margWeightSet w' s.1
      = pushWeight Q (margWeightSet w s.1)) :
    idensity a w' s E β = idensity a w s E β := by
  apply idensity_eq_of_marg_eq
  rw [hw', pushWeight_eq_of_isStationary Q _ hQ]

end AmbientTransport

/-! ## Brick TF-2b — the kill exhibit

**K-IDENSITY-FLOW FIRES HERE.** The blanket statement
"Idensity is invariant under ambient step dynamics" is
FALSE, proved at the smallest seat, in the house
countermodel form (as K-TRID-DETERMINATION's banked
exhibit): κ = Fin 2, X = fun _ => Fin 2, region {0} under
the off-diagonal adjacency (boundary card 1 — the subtype
speaks), the uniform ambient weight, and the
concentrating kernel that pushes all mass onto the
configurations whose value at site 0 is 1. The marginal
moves from uniform (region entropy log 2) to the delta
at 1 (region entropy 0); the denominator stands at 1; so
component 1 of the pair moves.

**What the kill closes:** blanket flow-invariance of
Idensity, in every later text, post, and header — the
full reading of "invariant" may never be worn as
"invariant under dynamics" without TF-2a's condition on
its face. **What survives it:** TF-1 (own flow, own seat)
and TF-2a (marginal-preserving / stationary cases) — the
kill is aimed at the blanket form only, and says so. -/

section KillExhibit

/-- The exhibit's adjacency: off-diagonal on `Fin 2`. -/
def flowExhibitAdj : Fin 2 → Fin 2 → ℝ :=
  fun x y => if x ≠ y then 1 else 0

/-- The exhibit's ambient weight: uniform on the four
    configurations. -/
noncomputable def flowExhibitW : (∀ _ : Fin 2, Fin 2) → ℝ :=
  fun _ => 1 / 4

/-- The exhibit's kernel: every row spreads its mass
    uniformly over the two configurations whose value at
    site 0 is 1 — a stochastic concentrating kernel
    (each row sums to 1). -/
noncomputable def flowExhibitP : (∀ _ : Fin 2, Fin 2)
    → (∀ _ : Fin 2, Fin 2) → ℝ :=
  fun _ y => if y 0 = 1 then 1 / 2 else 0

/-- The exhibit's boundary: the vertex boundary of `{0}`
    under the off-diagonal adjacency is `{1}`, card 1 —
    the subtype in the headline speaks. -/
theorem flowExhibit_boundaryCard :
    boundaryCard flowExhibitAdj {0} = 1 := by
  have h : vertexBoundary flowExhibitAdj {0} = {1} := by
    ext x
    fin_cases x <;> simp [mem_vertexBoundary, flowExhibitAdj]
  rw [boundaryCard, h, Finset.card_singleton]

/-- One step of the exhibit's kernel on the uniform
    weight: mass 1/2 on each configuration with value 1
    at site 0, 0 elsewhere. -/
theorem flowExhibit_push_apply :
    pushWeight flowExhibitP flowExhibitW
      = fun y => if y 0 = 1 then 1 / 2 else 0 := by
  funext y
  rw [pushWeight_apply]
  simp only [flowExhibitW, flowExhibitP]
  rw [← Finset.sum_mul]
  norm_num [Finset.sum_const, Fintype.card_pi, Fin.prod_univ_two]

/-- The exhibit's marginal before the step: uniform on
    the region's two configurations (the restricted fiber
    has card 2 — pure Fin data, decided in the kernel). -/
theorem flowExhibit_marg_uniform :
    margWeightSet flowExhibitW {0} = fun _ => 1 / 2 := by
  funext z
  have hcard : (Finset.univ.filter
      (fun y : (∀ _ : Fin 2, Fin 2) =>
        (fun i : ({0} : Finset (Fin 2)) => y i) = z)).card
      = 2 := by decide +revert
  rw [margWeightSet_apply]
  simp only [flowExhibitW]
  rw [Finset.sum_const, hcard]
  norm_num

/-- The exhibit's marginal after the step: the delta at
    the region configuration with value 1 at site 0. -/
theorem flowExhibit_marg_pushed :
    margWeightSet (pushWeight flowExhibitP flowExhibitW) {0}
      = fun z => if z ⟨0, Finset.mem_singleton_self 0⟩ = 1
          then 1 else 0 := by
  funext z
  have hcard : (Finset.univ.filter
      (fun y : (∀ _ : Fin 2, Fin 2) =>
        (fun i : ({0} : Finset (Fin 2)) => y i) = z)).card
      = 2 := by decide +revert
  have hterm : ∀ y ∈ Finset.univ.filter
        (fun y : (∀ _ : Fin 2, Fin 2) =>
          (fun i : ({0} : Finset (Fin 2)) => y i) = z),
      (if y 0 = 1 then (1 : ℝ) / 2 else 0)
        = if z ⟨0, Finset.mem_singleton_self 0⟩ = 1
            then 1 / 2 else 0 := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have hy0 : y 0 = z ⟨0, Finset.mem_singleton_self 0⟩ :=
      congrFun hy.2 ⟨0, Finset.mem_singleton_self 0⟩
    rw [hy0]
  rw [margWeightSet_apply]
  simp only [flowExhibit_push_apply]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard]
  split_ifs <;> norm_num

/-- The exhibit's region entropy before the step:
    `log 2`. -/
theorem flowExhibit_entropy_uniform :
    regionEntropy flowExhibitW {0} = Real.log 2 := by
  have hcard : (Finset.univ :
      Finset (∀ i : ({0} : Finset (Fin 2)), Fin 2)).card
      = 2 := by decide
  rw [regionEntropy, flowExhibit_marg_uniform]
  unfold entropyW
  show -(∑ _z : (∀ i : ({0} : Finset (Fin 2)), Fin 2),
      (1 / 2 : ℝ) * Real.log (1 / 2)) = Real.log 2
  rw [Finset.sum_const, hcard]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-- The exhibit's region entropy after the step: `0` —
    every entropy summand of a delta weight vanishes
    (at the mass point `1 * log 1 = 0`; elsewhere
    `0 * log 0 = 0`, Mathlib's convention). -/
theorem flowExhibit_entropy_pushed :
    regionEntropy (pushWeight flowExhibitP flowExhibitW) {0}
      = 0 := by
  rw [regionEntropy, flowExhibit_marg_pushed]
  unfold entropyW
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro z _
  show (if z ⟨0, Finset.mem_singleton_self 0⟩ = 1
        then (1 : ℝ) else 0)
      * Real.log (if z ⟨0, Finset.mem_singleton_self 0⟩ = 1
        then 1 else 0) = 0
  by_cases hz : z ⟨0, Finset.mem_singleton_self 0⟩ = 1
    <;> simp [hz]

/-- **K-IDENSITY-FLOW — the kill** (Tier T1 — proved
    negative): Idensity is NOT invariant under ambient
    step dynamics. At the exhibit seat, one concentrating
    step moves the pair's first component from `log 2`
    to `0` over a standing denominator of `1`. Blanket
    flow-invariance is false; the surviving forms are
    TF-1's (own flow at the own seat) and TF-2a's
    (marginal-preserving / stationary dynamics), each
    with its condition on its face. -/
theorem idensity_not_flow_invariant :
    ∃ (a : Fin 2 → Fin 2 → ℝ) (w : (∀ _ : Fin 2, Fin 2) → ℝ)
      (s : {s : Finset (Fin 2) // boundaryCard a s ≠ 0})
      (E : (∀ i : s.1, Fin 2) → ℝ) (β : ℝ)
      (P : (∀ _ : Fin 2, Fin 2) → (∀ _ : Fin 2, Fin 2) → ℝ),
      idensity a (pushWeight P w) s E β
        ≠ idensity a w s E β := by
  refine ⟨flowExhibitAdj, flowExhibitW,
    ⟨{0}, by rw [flowExhibit_boundaryCard]; exact one_ne_zero⟩,
    0, 1, flowExhibitP, ?_⟩
  intro hcon
  have h1 := congrArg Prod.fst hcon
  rw [idensity_fst, idensity_fst, flowExhibit_entropy_pushed,
    flowExhibit_entropy_uniform, flowExhibit_boundaryCard]
    at h1
  simp only [Nat.cast_one, div_one] at h1
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' h1.symm

end KillExhibit

end ThetLogos
