import Mathlib.Analysis.InnerProductSpace.LinearPMap
import ThetLogos.BosonicInteraction

namespace ThetLogos

open scoped LinearPMap

/-!
# ThetLogos.BosonicESA — Pitch 3, ESA-α: the sharp restatement

**Mandatory honesty clause.** This module does **not** prove essential
self-adjointness of the bosonic interacting Hamiltonian. It does exactly
what the parked-fleet gauntlet priced as ESA-α (S): it restates Pitch 3's
sole remaining clause in sharp form using Mathlib's `LinearPMap.closure`
(the gauntlet's kill K2: the Campaign 2 dossier sentence "Mathlib has no
LinearPMap closure operator" is dead — the operator exists at
`Mathlib/Topology/Algebra/Module/LinearPMap.lean:94`), proves everything
about that restatement that follows from Campaign 2's results by pure
order/graph arguments, and fences by name the one input that does not
follow: the von Neumann double-adjoint identity `T†† = T.closure`, which
is **absent** from the pinned Mathlib (no `LinearPMap.adjoint_adjoint`;
grep-verified 2026-10-17). The proof of the target itself is ESA-β,
priced M–L via the banded route R2; its map is in the dossier
`whitepaper/esa-alpha-2026-10-17.md`. Nothing here upgrades any Pitch 3
headline: essential self-adjointness remains unproved.

Contents:
- §0: a closed partial map equals its own closure (pure topology).
- §1: for a densely defined symmetric `T` (i.e. `T ≤ T†`): `T` is
  closable and `T.closure ≤ T†`; hence the ESA statement
  `T.closure = T†` is equivalent to the single inclusion
  `T† ≤ T.closure`.
- §2: the adjoint of the closure is the adjoint (graph argument), giving
  the `IsSelfAdjoint T.closure` reformulation and the direction
  ESA ⇒ `T† ≤ T††`; the converse direction is stated conditionally on
  the fenced von Neumann identity.
- §3: instantiation to `hamPMap`: the named target `BosonicESA` and its
  proved restatements.
-/

-- ============================================================================
-- §0. A closed partial map is its own closure
-- ============================================================================

section ClosedClosure

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [AddCommGroup F]
  [Module R E] [Module R F] [TopologicalSpace E] [TopologicalSpace F]
  [ContinuousAdd E] [ContinuousAdd F] [TopologicalSpace R]
  [ContinuousSMul R E] [ContinuousSMul R F]

/-- A closed partial linear map equals its own closure: the graph is
already topologically closed, so the closure construction returns the
same graph. (Not in Mathlib's API as a standalone statement.) -/
theorem closed_closure_eq_self {f : E →ₗ.[R] F} (hf : f.IsClosed) :
    f.closure = f := by
  apply LinearPMap.eq_of_eq_graph
  rw [← hf.isClosable.graph_closure_eq_closure_graph,
    hf.submodule_topologicalClosure_eq]

end ClosedClosure

-- ============================================================================
-- §1. The symmetric package: closability and `closure ≤ adjoint`
-- ============================================================================

section Symmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {T : E →ₗ.[𝕜] E}

/-- A densely defined symmetric partial map is closable: its adjoint is
a closed extension (`LinearPMap.adjoint_isClosed`), and a map with a
closed extension is closable. -/
theorem symmetric_isClosable (hT : Dense (T.domain : Set E)) (h : T ≤ T†) :
    T.IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨T†, LinearPMap.adjoint_isClosed hT, h⟩

/-- For a densely defined symmetric partial map, the closure is
contained in the adjoint: the adjoint is a closed extension, hence it
contains the smallest closed extension. -/
theorem symmetric_closure_le_adjoint (hT : Dense (T.domain : Set E))
    (h : T ≤ T†) : T.closure ≤ T† :=
  (LinearPMap.IsClosable.closure_mono (LinearPMap.adjoint_isClosed hT).isClosable h).trans_eq
    (closed_closure_eq_self (LinearPMap.adjoint_isClosed hT))

/-- **The ESA restatement, general form.** For a densely defined
symmetric partial map, essential self-adjointness in closure form
(`T.closure = T†`) is equivalent to the single remaining inclusion
`T† ≤ T.closure` — the other inclusion is §1's theorem. -/
theorem closure_eq_adjoint_iff_adjoint_le_closure
    (hT : Dense (T.domain : Set E)) (h : T ≤ T†) :
    T.closure = T† ↔ T† ≤ T.closure :=
  ⟨fun he => le_of_eq he.symm,
   fun hle => le_antisymm (symmetric_closure_le_adjoint hT h) hle⟩

end Symmetric

-- ============================================================================
-- §2. The adjoint of the closure, and the `T† ≤ T††` form
-- ============================================================================

section AdjointClosure

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace E]
variable {T : E →ₗ.[𝕜] F}

/-- The pairing condition defining membership in `g.adjoint`
(`Submodule.mem_adjoint_iff`) is a closed condition on `E × F`, so the
adjoint of a graph does not see its topological closure. (Graph-level
input to `adjoint_closure_eq_adjoint`; not in Mathlib's API.) -/
theorem submodule_adjoint_topologicalClosure_eq (g : Submodule 𝕜 (E × F)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_adjoint_iff] at hx ⊢
    exact fun a b hab => hx a b (g.le_topologicalClosure hab)
  · intro x hx
    rw [Submodule.mem_adjoint_iff] at hx ⊢
    intro a b hab
    have hcont : Continuous (fun p : E × F =>
        inner 𝕜 p.2 x.1 - inner 𝕜 p.1 x.2) :=
      (continuous_snd.inner continuous_const).sub
        (continuous_fst.inner continuous_const)
    have hCclosed : IsClosed {p : E × F | inner 𝕜 p.2 x.1 - inner 𝕜 p.1 x.2 = 0} :=
      isClosed_eq hcont continuous_const
    have hgC : (g : Set (E × F)) ⊆
        {p : E × F | inner 𝕜 p.2 x.1 - inner 𝕜 p.1 x.2 = 0} :=
      fun p hp => hx p.1 p.2 (Prod.mk.eta ▸ hp)
    have hab' : ((a, b) : E × F) ∈ closure (g : Set (E × F)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact SetLike.mem_coe.mpr hab
    exact closure_minimal hgC hCclosed hab'

/-- The domain of the closure is dense when the domain is: the closure
extends `T` (`LinearPMap.le_closure`). -/
theorem dense_domain_closure (hT : Dense (T.domain : Set E)) :
    Dense (T.closure.domain : Set E) :=
  hT.mono (SetLike.coe_subset_coe.mpr (LinearPMap.le_closure T).1)

/-- **The adjoint of the closure is the adjoint.** For a densely
defined partial map, `(T.closure)† = T†`: both adjoints have the same
graph, since a graph and its closure have the same adjoint
(`submodule_adjoint_topologicalClosure_eq`). This is the
"adjoint depends only on the closure" half of von Neumann's theorem —
the half that is pure graph theory. -/
theorem adjoint_closure_eq_adjoint (hT : Dense (T.domain : Set E)) :
    (T.closure)† = T† := by
  by_cases hcl : T.IsClosable
  · apply LinearPMap.eq_of_eq_graph
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_domain_closure hT),
      ← hcl.graph_closure_eq_closure_graph,
      submodule_adjoint_topologicalClosure_eq,
      ← LinearPMap.adjoint_graph_eq_graph_adjoint hT]
  · rw [LinearPMap.closure_def' hcl]

end AdjointClosure

section SymmetricConsequences

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {T : E →ₗ.[𝕜] E}

/-- The ESA statement is equivalently the self-adjointness of the
closure: `IsSelfAdjoint T.closure` unfolds to `(T.closure)† = T.closure`,
and the adjoint of the closure is the adjoint (§2). No symmetry
hypothesis is needed for this reformulation. -/
theorem closure_eq_adjoint_iff_isSelfAdjoint_closure
    (hT : Dense (T.domain : Set E)) :
    T.closure = T† ↔ IsSelfAdjoint T.closure := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_closure_eq_adjoint hT]
  exact eq_comm

/-- ESA implies the adjoint is symmetric, in the form `T† ≤ T††`: if
`T.closure = T†`, then `T†† = (T.closure)† = T†` by §2, so the
inclusion is equality. -/
theorem adjoint_le_adjoint_adjoint_of_closure_eq_adjoint
    (hT : Dense (T.domain : Set E)) (he : T.closure = T†) :
    T† ≤ T†† := by
  have h2 : T†† = T† := by
    conv_lhs => rw [← he]
    exact adjoint_closure_eq_adjoint hT
  exact le_of_eq h2.symm

/-- The converse direction, **fenced**: it is exactly the von Neumann
double-adjoint identity `T†† = T.closure`, which is absent from the
pinned Mathlib (no `LinearPMap.adjoint_adjoint`). Given that identity
as a hypothesis, adjoint-symmetry `T† ≤ T††` does close the ESA
statement. ESA-β does not route through this identity (see the
dossier); it is recorded here so the fence has a precise address. -/
theorem closure_eq_adjoint_of_adjoint_le_adjoint_adjoint
    (hT : Dense (T.domain : Set E)) (h : T ≤ T†)
    (hVN : T†† = T.closure) (hiii : T† ≤ T††) : T.closure = T† := by
  rw [hVN] at hiii
  exact le_antisymm (symmetric_closure_le_adjoint hT h) hiii

/-- The full three-way equivalence, conditional on the fenced von
Neumann identity: under `T†† = T.closure`, ESA (`T.closure = T†`) is
equivalent to adjoint-symmetry (`T† ≤ T††`). -/
theorem closure_eq_adjoint_iff_adjoint_le_adjoint_adjoint_of_doubleAdjoint
    (hT : Dense (T.domain : Set E)) (h : T ≤ T†) (hVN : T†† = T.closure) :
    T.closure = T† ↔ T† ≤ T†† :=
  ⟨fun he => adjoint_le_adjoint_adjoint_of_closure_eq_adjoint hT he,
   fun hiii => closure_eq_adjoint_of_adjoint_le_adjoint_adjoint hT h hVN hiii⟩

end SymmetricConsequences

-- ============================================================================
-- §3. Instantiation: the named target `BosonicESA`
-- ============================================================================

section Bosonic

/-- **BosonicESA — the sharp form of Pitch 3's sole remaining clause.**

Essential self-adjointness of the bosonic interacting Hamiltonian,
stated with Mathlib's closure operator: the closure of Campaign 2's
`hamPMap` equals its adjoint. This is a *statement*, not a theorem:
nothing in this module or the corpus proves it. It is equivalent (by
the proved restatements below) to the single inclusion
`(hamPMap d lam W g)† ≤ (hamPMap d lam W g).closure`, and to
`IsSelfAdjoint (hamPMap d lam W g).closure`. Its proof is ESA-β
(priced M–L, banded route R2 — see the dossier). Until it lands, no
text may call the bosonic Hamiltonian self-adjoint without one of
Campaign 2's three scoped senses attached. -/
def BosonicESA (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) : Prop :=
  (hamPMap d lam W g).closure = (hamPMap d lam W g)†

/-- The bosonic Hamiltonian partial map is closable: its adjoint is a
closed extension (Campaign 2's `hamPMap_le_adjoint` + §1). -/
theorem hamPMap_isClosable (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    (hamPMap d lam W g).IsClosable :=
  symmetric_isClosable (dom_dense d) (hamPMap_le_adjoint d lam W g)

/-- The closure of the bosonic Hamiltonian is contained in its adjoint
(§1 instantiated): one of the two inclusions of `BosonicESA` is
already a theorem. -/
theorem hamPMap_closure_le_adjoint (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    (hamPMap d lam W g).closure ≤ (hamPMap d lam W g)† :=
  symmetric_closure_le_adjoint (dom_dense d) (hamPMap_le_adjoint d lam W g)

/-- The closure of the bosonic Hamiltonian is a closed operator. -/
theorem hamPMap_closure_isClosed (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    (hamPMap d lam W g).closure.IsClosed :=
  (hamPMap_isClosable d lam W g).closure_isClosed

/-- **The target, restated.** `BosonicESA` is equivalent to the single
remaining inclusion: the adjoint is contained in the closure. -/
theorem bosonicESA_iff_adjoint_le_closure (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    BosonicESA d lam W g ↔
      (hamPMap d lam W g)† ≤ (hamPMap d lam W g).closure :=
  closure_eq_adjoint_iff_adjoint_le_closure (dom_dense d)
    (hamPMap_le_adjoint d lam W g)

/-- **The target, restated (self-adjoint-closure form).** `BosonicESA`
is equivalent to self-adjointness of the closure. -/
theorem bosonicESA_iff_isSelfAdjoint_closure (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    BosonicESA d lam W g ↔ IsSelfAdjoint (hamPMap d lam W g).closure :=
  closure_eq_adjoint_iff_isSelfAdjoint_closure (dom_dense d)

/-- One direction of the adjoint-symmetry form is already free:
`BosonicESA` would imply `(hamPMap d lam W g)† ≤ (hamPMap d lam W g)††`
(§2). The converse is fenced behind the von Neumann double-adjoint
identity, absent from Mathlib — see
`closure_eq_adjoint_iff_adjoint_le_adjoint_adjoint_of_doubleAdjoint`. -/
theorem bosonicESA_adjoint_le_adjoint_adjoint (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    BosonicESA d lam W g →
      (hamPMap d lam W g)† ≤ (hamPMap d lam W g)†† :=
  fun he => adjoint_le_adjoint_adjoint_of_closure_eq_adjoint (dom_dense d) he

end Bosonic

#print axioms closed_closure_eq_self
#print axioms symmetric_closure_le_adjoint
#print axioms closure_eq_adjoint_iff_adjoint_le_closure
#print axioms adjoint_closure_eq_adjoint
#print axioms closure_eq_adjoint_iff_isSelfAdjoint_closure
#print axioms bosonicESA_iff_adjoint_le_closure
#print axioms bosonicESA_iff_isSelfAdjoint_closure

end ThetLogos
